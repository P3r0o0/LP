import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Hadamard
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Topology.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.Convex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Complex.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Distribution.Distribution
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

open Complex Filter Topology Set ContinuousLinearMap ContinuousMultilinearMap MeasureTheory
open intervalIntegral
open scoped Distributions FourierTransform RealInnerProductSpace NNReal

namespace Analysis

lemma complex_multilinear_zero_of_real_zero_N {ι : Type*} [Finite ι] (k : ℕ)
    (p : ContinuousMultilinearMap ℂ (fun _ : Fin k => (ι → ℂ)) ℂ)
    (ofRealN : (ι → ℝ) →L[ℝ] (ι → ℂ))
    (h_ofReal : ∀ x : ι → ℝ, ofRealN x = (fun i => (x i : ℂ)))
    (h : ∀ x : Fin k → (ι → ℝ), p (fun i => ofRealN (x i)) = 0) :
    p = 0 := by
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  classical
  haveI := Fintype.ofFinite ι
  apply Module.Basis.ext_multilinear (fun _ => Pi.basisFun ℂ ι)
  intro v
  have hx : ∀ j, (Pi.basisFun ℂ ι) (v j) = ofRealN (Pi.basisFun ℝ ι (v j)) := by
    intro j
    rw [h_ofReal]
    ext i
    dsimp [Pi.basisFun]
    by_cases hij : v j = i
    · simp [hij]
    · simp [hij]
  have h_eq : (fun j => (Pi.basisFun ℂ ι) (v j)) = (fun j => ofRealN (Pi.basisFun ℝ ι (v j))) := by
    ext j i
    rw [hx j]
  rw [h_eq]
  exact h (fun j => Pi.basisFun ℝ ι (v j))

lemma tendsto_ofReal_ne (a : ℝ) : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[≠] a) (𝓝[≠] (a : ℂ)) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · exact continuous_ofReal.continuousAt.tendsto.comp nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact ofReal_inj.not.mpr hx

lemma freq_zero_of_real_zero (h : ℂ → ℂ) (a : ℝ) (h_sub : ∀ᶠ t : ℝ in 𝓝 a, h (t : ℂ) = 0) :
    ∃ᶠ z in 𝓝[≠] (a : ℂ), h z = 0 := by
  have h_sub_ne : ∀ᶠ t : ℝ in 𝓝[≠] a, h (t : ℂ) = 0 := nhdsWithin_le_nhds h_sub
  have h_ne_bot : (𝓝[≠] a).NeBot := PerfectSpace.not_isolated a
  have h_freq_real : Filter.Frequently (fun (t : ℝ) => h (t : ℂ) = 0) (𝓝[≠] a) :=
    h_sub_ne.frequently
  have h_tendsto := tendsto_ofReal_ne a
  exact h_tendsto.frequently h_freq_real

lemma analytic_nhds_eq_of_real_eq_1D (f g : ℂ → ℂ) (a : ℝ)
    (hf : AnalyticAt ℂ f (a : ℂ)) (hg : AnalyticAt ℂ g (a : ℂ))
    (h_real : ∀ᶠ t : ℝ in 𝓝 a, f (t : ℂ) = g (t : ℂ)) :
    ∀ᶠ z : ℂ in 𝓝 (a : ℂ), f z = g z := by
  have hfg : AnalyticAt ℂ (f - g) (a : ℂ) := hf.sub hg
  have h_sub : ∀ᶠ t : ℝ in 𝓝 a, (f - g) (t : ℂ) = 0 := by
    filter_upwards [h_real] with t ht
    simp [ht]
  have h_freq := freq_zero_of_real_zero (f - g) a h_sub
  have h_zero_or_freq := hfg.eventually_eq_zero_or_eventually_ne_zero
  cases h_zero_or_freq with
  | inl h_zero =>
    filter_upwards [h_zero] with z hz
    exact sub_eq_zero.mp hz
  | inr h_ne =>
    exact (h_freq h_ne).elim

lemma symm_multilinear_real_eq_zero_of_diagonal_zero_N {ι : Type*} [Finite ι] {n : ℕ}
    (p : ContinuousMultilinearMap ℝ (fun _ : Fin n => (ι → ℝ)) ℂ)
    (h_symm : ∀ (σ : Equiv.Perm (Fin n)) (v : Fin n → (ι → ℝ)), p (fun i => v (σ i)) = p v)
    (h_diag : ∀ x : (ι → ℝ), p (fun _ => x) = 0) :
    p = 0 := by
  haveI := Fintype.ofFinite ι
  apply ContinuousMultilinearMap.ext
  intro v
  have h_func_zero : (fun x : (ι → ℝ) => p (fun _ => x)) = fun _ => 0 := by
    ext x; exact h_diag x
  have h_deriv : iteratedFDeriv ℝ n (fun x : (ι → ℝ) => p (fun _ => x)) 0 v = 0 := by
    rw [h_func_zero]
    rw [iteratedFDeriv_fun_zero]
    simp
  have h_deriv_diag := p.iteratedFDeriv_comp_diagonal 0 v
  rw [h_deriv] at h_deriv_diag
  have h_sum : (∑ σ : Equiv.Perm (Fin n), p (fun i => v (σ i))) = (Nat.factorial n) • (p v) := by
    have h_symm_eval : ∀ σ : Equiv.Perm (Fin n), p (fun i => v (σ i)) = p v := fun σ => h_symm σ v
    rw [Finset.sum_congr rfl (fun σ _ => h_symm_eval σ)]
    rw [Finset.sum_const]
    rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  rw [h_sum] at h_deriv_diag
  have h_smul_zero := h_deriv_diag.symm
  cases smul_eq_zero.mp h_smul_zero with
  | inl h =>
    have h2 : Nat.factorial n = 0 := Nat.cast_eq_zero.mp h
    exfalso
    exact Nat.factorial_ne_zero n h2
  | inr h => exact h

lemma complex_multilinear_zero_of_diagonal_real_zero_N {ι : Type*} [Finite ι] {n : ℕ}
    (p : ContinuousMultilinearMap ℂ (fun _ : Fin n => (ι → ℂ)) ℂ)
    (h_symm : ∀ (σ : Equiv.Perm (Fin n)) (v : Fin n → (ι → ℂ)), p (fun i => v (σ i)) = p v)
    (ofRealN : (ι → ℝ) →L[ℝ] (ι → ℂ))
    (h_ofReal : ∀ x : ι → ℝ, ofRealN x = (fun i => (x i : ℂ)))
    (h_diag : ∀ x : (ι → ℝ), p (fun _ => ofRealN x) = 0) :
    p = 0 := by
  haveI := Fintype.ofFinite ι
  let p_real := (p.restrictScalars ℝ).compContinuousLinearMap (fun _ => ofRealN)
  have h_symm_real :
      ∀ (σ : Equiv.Perm (Fin n)) (v : Fin n → (ι → ℝ)), p_real (fun i => v (σ i)) = p_real v := by
    intro σ v
    exact h_symm σ (fun i => ofRealN (v i))
  have h_diag_real : ∀ x : (ι → ℝ), p_real (fun _ => x) = 0 := h_diag
  have p_real_zero :=
    symm_multilinear_real_eq_zero_of_diagonal_zero_N p_real h_symm_real h_diag_real
  have h_eval : ∀ v : Fin n → (ι → ℝ), p (fun i => ofRealN (v i)) = 0 := by
    intro v
    have h_zero : p_real v = (0 : ContinuousMultilinearMap ℝ (fun _ : Fin n => (ι → ℝ)) ℂ) v := by
      rw [p_real_zero]
    exact h_zero
  exact complex_multilinear_zero_of_real_zero_N n p ofRealN h_ofReal h_eval

lemma ftaylorSeries_isSymmetric {ι : Type*} [Fintype ι] {n : ℕ} (f : (ι → ℂ) → ℂ) (a : ι → ℂ)
    (hf : AnalyticAt ℂ f a) :
    ∀ (σ : Equiv.Perm (Fin n)) (v : Fin n → (ι → ℂ)),
      (ftaylorSeries ℂ f a) n (fun i => v (σ i)) = (ftaylorSeries ℂ f a) n v := by
  intro σ v
  have h_cont : ContDiffAt ℂ ⊤ f a := hf.contDiffAt
  exact h_cont.iteratedFDeriv_comp_perm v σ

lemma ftaylorSeries_diag_zero {ι : Type*} [Fintype ι] {n : ℕ} (f : (ι → ℂ) → ℂ) (a : ι → ℂ)
    (hf : AnalyticAt ℂ f a)
    (ofRealN : (ι → ℝ) →L[ℝ] (ι → ℂ))
    (h_ofReal : ∀ x : ι → ℝ, ofRealN x = (fun i => (x i : ℂ)))
    (h_real : ∀ᶠ t : ι → ℝ in 𝓝 0, f (a + ofRealN t) = 0) :
    ∀ x : (ι → ℝ), (ftaylorSeries ℂ f a) n (fun _ => ofRealN x) = 0 := by
  intro x
  rcases hf with ⟨p, hp⟩
  let L : ℂ →L[ℂ] (ι → ℂ) := ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (ofRealN x)
  have hp_shifted := hp.comp_sub (-a)
  have h_add : (a + -a) = 0 := add_neg_cancel a
  rw [h_add] at hp_shifted
  have h_simp : (fun z => f (z - -a)) = (fun z => f (a + z)) := by
    ext z
    rw [sub_neg_eq_add, add_comm]
  rw [h_simp] at hp_shifted
  have h_L_zero : L 0 = 0 := ContinuousLinearMap.map_zero L
  have hp_shifted2 : HasFPowerSeriesAt (fun z => f (a + z)) p (L 0) := by
    rw [h_L_zero]
    exact hp_shifted
  have hp_comp : HasFPowerSeriesAt (fun z => f (a + L z)) (p.compContinuousLinearMap L) 0 := by
    exact HasFPowerSeriesAt.compContinuousLinearMap (u := L) hp_shifted2
  have h_g_real : ∀ᶠ t : ℝ in 𝓝 0, f (a + L (t : ℂ)) = (fun _ : ℂ => (0 : ℂ)) t := by
    let φ : ℝ → (ι → ℝ) := fun t => t • x
    have h_φ_cont : Continuous φ := continuous_id.smul continuous_const
    have h_φ_zero : φ 0 = 0 := zero_smul ℝ x
    have h_tendsto := Continuous.tendsto h_φ_cont 0
    rw [h_φ_zero] at h_tendsto
    have h_eventually := h_tendsto.eventually h_real
    refine h_eventually.mono ?_
    intro t ht
    have h_L_t : L (t : ℂ) = (t : ℂ) • ofRealN x := rfl
    rw [h_L_t]
    have h_smul : (t : ℂ) • ofRealN x = ofRealN (t • x) := by
      ext i
      rw [h_ofReal, h_ofReal]
      simp only [Pi.smul_apply, smul_eq_mul]
      push_cast
      rfl
    rw [h_smul]
    exact ht
  have h_g_zero : ∀ᶠ z : ℂ in 𝓝 0, f (a + L z) = 0 := by
    have h_g_ana : AnalyticAt ℂ (fun z => f (a + L z)) (0 : ℝ) := ⟨_, hp_comp⟩
    have h_zero_ana : AnalyticAt ℂ (fun _ : ℂ => (0 : ℂ)) (0 : ℝ) := analyticAt_const
    exact analytic_nhds_eq_of_real_eq_1D (fun z => f (a + L z)) (fun _ => 0) (0 : ℝ)
      h_g_ana h_zero_ana h_g_real
  have h_p_comp_zero : p.compContinuousLinearMap L = 0 := by
    exact HasFPowerSeriesAt.eq_zero_of_eventually hp_comp h_g_zero
  have h_pn_comp_zero : (p.compContinuousLinearMap L) n = 0 := by
    rw [h_p_comp_zero]; rfl
  have h_eval : (p.compContinuousLinearMap L) n (fun _ => 1) = p n (fun _ => L 1) := rfl
  have h_L_1 : L 1 = ofRealN x := by simp [L]
  rw [h_L_1] at h_eval
  rw [h_pn_comp_zero] at h_eval
  have h_p_zero : p n (fun _ => ofRealN x) = 0 := h_eval.symm
  rcases hp with ⟨r, hp_ball⟩
  have h_sum := hp_ball.iteratedFDeriv_eq_sum_of_completeSpace (n := n) (fun _ => ofRealN x)
  have h_sum_const : (∑ σ : Equiv.Perm (Fin n), p n (fun _ : Fin n => ofRealN x)) =
      (Fintype.card (Equiv.Perm (Fin n))) • p n (fun _ => ofRealN x) := by
    exact Finset.sum_const _
  rw [h_sum_const, h_p_zero] at h_sum
  have h_smul_zero : (Fintype.card (Equiv.Perm (Fin n))) • (0 : ℂ) = 0 := smul_zero _
  rw [h_smul_zero] at h_sum
  exact h_sum

lemma eq_zero_of_ftaylorSeries_zero {ι : Type*} [Fintype ι] (f : (ι → ℂ) → ℂ) (a : ι → ℂ)
    (hf : AnalyticAt ℂ f a)
    (h_zero : ∀ n, (ftaylorSeries ℂ f a) n = 0) :
    ∀ᶠ z in 𝓝 a, f z = 0 := by
  rcases hf with ⟨p, hp⟩
  rcases hp with ⟨r, hp_ball⟩
  have h_p_diag : ∀ n y, p n (fun _ => y) = 0 := by
    intro n y
    have h_sum := hp_ball.iteratedFDeriv_eq_sum_of_completeSpace (n := n) (fun _ => y)
    have hz := h_zero n
    have h_iter : iteratedFDeriv ℂ n f a = 0 := hz
    rw [h_iter] at h_sum
    have h_eval_zero :
        (0 : ContinuousMultilinearMap ℂ (fun _ : Fin n => (ι → ℂ)) ℂ) (fun _ => y) = 0 := rfl
    rw [h_eval_zero] at h_sum
    have h_sum_const : (∑ σ : Equiv.Perm (Fin n), p n (fun _ : Fin n => y)) =
        (Fintype.card (Equiv.Perm (Fin n))) • p n (fun _ => y) := by
      exact Finset.sum_const _
    rw [h_sum_const] at h_sum
    have h_card : Fintype.card (Equiv.Perm (Fin n)) = n.factorial := by
      rw [Fintype.card_perm, Fintype.card_fin]
    rw [h_card] at h_sum
    have h_symm_eq : (n.factorial) • p n (fun _ => y) = 0 := h_sum.symm
    have h_fact : n.factorial ≠ 0 := n.factorial_ne_zero
    cases smul_eq_zero.mp h_symm_eq with
    | inl h => contradiction
    | inr h => exact h
  filter_upwards [hp_ball.eventually_hasSum_sub] with z hz
  have h_zero_seq : (fun n : ℕ => p n (fun _ : Fin n => z - a)) = (fun _ : ℕ => 0) := by
    ext n
    exact h_p_diag n (z - a)
  rw [h_zero_seq] at hz
  have h_zero_sum : HasSum (fun _ : ℕ => (0 : ℂ)) 0 := hasSum_zero
  exact hz.unique h_zero_sum

lemma analytic_nhds_eq_of_real_eq_N {ι : Type*} [Fintype ι] (f g : (ι → ℂ) → ℂ)
    (a : ι → ℝ) (ofRealN : (ι → ℝ) →L[ℝ] (ι → ℂ))
    (h_ofReal : ∀ x : ι → ℝ, ofRealN x = (fun i => (x i : ℂ)))
    (hf : AnalyticAt ℂ f (ofRealN a)) (hg : AnalyticAt ℂ g (ofRealN a))
    (h_real : ∀ᶠ t : ι → ℝ in 𝓝 a, f (ofRealN t) = g (ofRealN t)) :
    ∀ᶠ z : ι → ℂ in 𝓝 (ofRealN a), f z = g z := by
  have hfg : AnalyticAt ℂ (f - g) (ofRealN a) := hf.sub hg
  have hp_zero : ∀ n, (ftaylorSeries ℂ (f - g) (ofRealN a)) n = 0 := by
    intro n
    have h_symm := ftaylorSeries_isSymmetric (n := n) (f - g) (ofRealN a) hfg
    have h_real_zero : ∀ᶠ t : ι → ℝ in 𝓝 0, (f - g) (ofRealN a + ofRealN t) = 0 := by
      have h_cont : Continuous (fun t : ι → ℝ => a + t) := continuous_const.add continuous_id
      have h_tendsto := h_cont.tendsto 0
      have h_zero : a + 0 = a := add_zero a
      rw [h_zero] at h_tendsto
      have h_ev := h_tendsto.eventually h_real
      refine h_ev.mono ?_
      intro t ht
      have h_lin : ofRealN (a + t) = ofRealN a + ofRealN t := ofRealN.map_add a t
      rw [← h_lin]
      exact sub_eq_zero.mpr ht
    have h_diag :=
      ftaylorSeries_diag_zero (n := n) (f - g) (ofRealN a) hfg ofRealN h_ofReal h_real_zero
    exact complex_multilinear_zero_of_diagonal_real_zero_N
      ((ftaylorSeries ℂ (f - g) (ofRealN a)) n) h_symm ofRealN h_ofReal h_diag
  have h_zero_nhds := eq_zero_of_ftaylorSeries_zero (f - g) (ofRealN a) hfg hp_zero
  filter_upwards [h_zero_nhds] with z hz
  exact sub_eq_zero.mp hz

lemma analytic_eq_of_real_eq_R_N {ι : Type*} [Fintype ι] {U : Set (ι → ℂ)}
    (_hU_open : IsOpen U) (hU_conn : IsConnected U)
    (f g : (ι → ℂ) → ℂ) (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U)
    (a : ι → ℝ) (ofRealN : (ι → ℝ) →L[ℝ] (ι → ℂ))
    (h_ofReal : ∀ x : ι → ℝ, ofRealN x = (fun i => (x i : ℂ)))
    (ha : ofRealN a ∈ U)
    (h_real : ∀ᶠ t : ι → ℝ in 𝓝 a, f (ofRealN t) = g (ofRealN t)) :
    Set.EqOn f g U := by
  have h_nhds_eq : ∀ᶠ z : ι → ℂ in 𝓝 (ofRealN a), f z = g z := by
    apply analytic_nhds_eq_of_real_eq_N f g a ofRealN h_ofReal (hf _ ha) (hg _ ha) h_real
  have hfg : AnalyticOnNhd ℂ (f - g) U := hf.sub hg
  have h_nhds_zero : ∀ᶠ z : ι → ℂ in 𝓝 (ofRealN a), (f - g) z = 0 := by
    filter_upwards [h_nhds_eq] with z hz
    simp [hz]
  have h_eq_zero :=
    hfg.eqOn_zero_of_preconnected_of_eventuallyEq_zero hU_conn.isPreconnected ha h_nhds_zero
  intro z hz
  have hz_zero := h_eq_zero hz
  exact sub_eq_zero.mp hz_zero

def upperHalfPlane : Set ℂ := {z | 0 < z.im}
def lowerHalfPlane : Set ℂ := {z | z.im < 0}

def slitDomain (I : Set ℝ) : Set ℂ := {z | z.im ≠ 0 ∨ z.re ∈ I}

lemma isOpen_slitDomain {I : Set ℝ} (hI : IsOpen I) : IsOpen (slitDomain I) := by
  have h1 : IsOpen {z : ℂ | z.im ≠ 0} := by
    have : {z : ℂ | z.im ≠ 0} = (fun z : ℂ => z.im) ⁻¹' {y : ℝ | y ≠ 0} := rfl
    rw [this]
    exact isOpen_ne.preimage continuous_im
  have h2 : IsOpen {z : ℂ | z.re ∈ I} := hI.preimage continuous_re
  exact IsOpen.union h1 h2

lemma wedgeIntegral_split_y (z w : ℂ) (y_mid : ℝ) (f : ℂ → ℂ)
    (hf_int_w : IntervalIntegrable (fun y => f (w.re + y * I)) volume z.im y_mid ∧
                IntervalIntegrable (fun y => f (w.re + y * I)) volume y_mid w.im)
    (hf_int_z : IntervalIntegrable (fun y => f (z.re + y * I)) volume z.im y_mid ∧
                IntervalIntegrable (fun y => f (z.re + y * I)) volume y_mid w.im) :
    wedgeIntegral z w f + wedgeIntegral w z f =
    (wedgeIntegral z (w.re + y_mid * I) f + wedgeIntegral (w.re + y_mid * I) z f) +
    (wedgeIntegral (z.re + y_mid * I) w f + wedgeIntegral w (z.re + y_mid * I) f) := by
  have h1 := wedgeIntegral_add_wedgeIntegral_eq z w f
  have h2 := wedgeIntegral_add_wedgeIntegral_eq z (w.re + y_mid * I) f
  have h3 := wedgeIntegral_add_wedgeIntegral_eq (z.re + y_mid * I) w f
  simp only [mul_re, mul_im, smul_eq_mul, add_re, add_im, ofReal_re, ofReal_im, I_re, I_im,
    sub_zero, zero_add, mul_zero, add_zero, mul_one] at h1 h2 h3
  rw [h1, h2, h3]
  have hw : (∫ (y : ℝ) in z.im..y_mid, f (↑w.re + ↑y * I)) +
      (∫ (y : ℝ) in y_mid..w.im, f (↑w.re + ↑y * I)) =
      (∫ (y : ℝ) in z.im..w.im, f (↑w.re + ↑y * I)) :=
    intervalIntegral.integral_add_adjacent_intervals hf_int_w.1 hf_int_w.2
  have hz : (∫ (y : ℝ) in z.im..y_mid, f (↑z.re + ↑y * I)) +
      (∫ (y : ℝ) in y_mid..w.im, f (↑z.re + ↑y * I)) =
      (∫ (y : ℝ) in z.im..w.im, f (↑z.re + ↑y * I)) :=
    intervalIntegral.integral_add_adjacent_intervals hf_int_z.1 hf_int_z.2
  generalize H1 : (∫ (x : ℝ) in z.re..w.re, f (↑x + ↑z.im * I)) = A at *
  generalize H2 : (∫ (x : ℝ) in z.re..w.re, f (↑x + ↑w.im * I)) = B at *
  generalize H3 : (∫ (x : ℝ) in z.re..w.re, f (↑x + ↑y_mid * I)) = C at *
  generalize H4 : (∫ (y : ℝ) in z.im..y_mid, f (↑w.re + ↑y * I)) = W1 at *
  generalize H5 : (∫ (y : ℝ) in y_mid..w.im, f (↑w.re + ↑y * I)) = W2 at *
  generalize H6 : (∫ (y : ℝ) in z.im..w.im, f (↑w.re + ↑y * I)) = W at *
  generalize H7 : (∫ (y : ℝ) in z.im..y_mid, f (↑z.re + ↑y * I)) = Z1 at *
  generalize H8 : (∫ (y : ℝ) in y_mid..w.im, f (↑z.re + ↑y * I)) = Z2 at *
  generalize H9 : (∫ (y : ℝ) in z.im..w.im, f (↑z.re + ↑y * I)) = Z at *
  have hw_subst : W = W1 + W2 := hw.symm
  have hz_subst : Z = Z1 + Z2 := hz.symm
  rw [hw_subst, hz_subst]
  ring

lemma wedgeIntegral_add_eq_zero_of_continuousOn_of_differentiableOn (f : ℂ → ℂ) (z w : ℂ)
    (Hc : ContinuousOn f (z.Rectangle w))
    (Hd : DifferentiableOn ℂ f
      (Ioo (min z.re w.re) (max z.re w.re) ×ℂ Ioo (min z.im w.im) (max z.im w.im))) :
    wedgeIntegral z w f + wedgeIntegral w z f = 0 := by
  rw [wedgeIntegral_add_wedgeIntegral_eq]
  exact integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn f z w Hc Hd

lemma intervalIntegrable_of_continuousOn_rect (z w : ℂ) (f : ℂ → ℂ) (x : ℝ)
    (hx : x ∈ uIcc z.re w.re) (y1 y2 : ℝ) (hy1 : y1 ∈ uIcc z.im w.im)
    (hy2 : y2 ∈ uIcc z.im w.im) (hf : ContinuousOn f (z.Rectangle w)) :
    IntervalIntegrable (fun y => f (x + y * I)) volume y1 y2 := by
  apply ContinuousOn.intervalIntegrable
  have h_comp : Continuous (fun y : ℝ => (x : ℂ) + (y : ℂ) * I) :=
    continuous_const.add (continuous_ofReal.mul continuous_const)
  have h_comp_on := h_comp.continuousOn (s := uIcc y1 y2)
  apply hf.comp h_comp_on
  intro y hy
  rw [Rectangle, mem_reProdIm]
  have h_re : ((x : ℂ) + (y : ℂ) * I).re = x := by simp
  have h_im : ((x : ℂ) + (y : ℂ) * I).im = y := by simp
  rw [h_re, h_im]
  refine ⟨hx, ?_⟩
  exact uIcc_subset_uIcc hy1 hy2 hy

lemma differentiableOn_split_y0 (f : ℂ → ℂ) (x1 x2 y : ℝ)
    (hf_ana_neg : AnalyticOn ℂ f lowerHalfPlane)
    (hf_ana_pos : AnalyticOn ℂ f upperHalfPlane) :
    DifferentiableOn ℂ f (Ioo x1 x2 ×ℂ Ioo (min y 0) (max y 0)) := by
  rcases lt_trichotomy y 0 with h | h | h
  · have h_min : min y 0 = y := min_eq_left h.le
    have h_max : max y 0 = 0 := max_eq_right h.le
    have h_sub : Ioo (min y 0) (max y 0) ⊆ Iio 0 := by
      rw [h_min, h_max]; intro t ht; exact ht.2
    have h_sub2 : Ioo x1 x2 ×ℂ Ioo (min y 0) (max y 0) ⊆ lowerHalfPlane := by
      intro z hz; rw [mem_reProdIm] at hz; exact h_sub hz.2
    exact hf_ana_neg.differentiableOn.mono h_sub2
  · have h_min : min y 0 = 0 := by rw [h]; exact min_self 0
    have h_max : max y 0 = 0 := by rw [h]; exact max_self 0
    have h_empty : Ioo (min y 0) (max y 0) = ∅ := by rw [h_min, h_max]; simp
    have h_empty2 : Ioo x1 x2 ×ℂ Ioo (min y 0) (max y 0) = ∅ := by
      ext z; simp [mem_reProdIm, h_empty]
    rw [h_empty2]; exact differentiableOn_empty
  · have h_min : min y 0 = 0 := min_eq_right h.le
    have h_max : max y 0 = y := max_eq_left h.le
    have h_sub : Ioo (min y 0) (max y 0) ⊆ Ioi 0 := by
      rw [h_min, h_max]; intro t ht; exact ht.1
    have h_sub2 : Ioo x1 x2 ×ℂ Ioo (min y 0) (max y 0) ⊆ upperHalfPlane := by
      intro z hz; rw [mem_reProdIm] at hz; exact h_sub hz.2
    exact hf_ana_pos.differentiableOn.mono h_sub2

theorem isConservativeOn_slitDomain (S : Set ℝ) (_hS : IsOpen S) (f : ℂ → ℂ)
    (hf_cont : ContinuousOn f (slitDomain S))
    (hf_ana_pos : AnalyticOn ℂ f upperHalfPlane)
    (hf_ana_neg : AnalyticOn ℂ f lowerHalfPlane) :
    IsConservativeOn f (slitDomain S) := by
  intro z w hzw
  rw [eq_neg_iff_add_eq_zero]
  have h_cont_rect : ContinuousOn f (z.Rectangle w) := hf_cont.mono hzw
  by_cases h0 : (0:ℝ) ∈ uIcc z.im w.im
  · have hf_int_w : IntervalIntegrable (fun y => f (w.re + y * I)) volume z.im 0 ∧
        IntervalIntegrable (fun y => f (w.re + y * I)) volume 0 w.im := by
      constructor
      · exact intervalIntegrable_of_continuousOn_rect z w f w.re right_mem_uIcc z.im 0
          left_mem_uIcc h0 h_cont_rect
      · exact intervalIntegrable_of_continuousOn_rect z w f w.re right_mem_uIcc 0 w.im
          h0 right_mem_uIcc h_cont_rect
    have hf_int_z : IntervalIntegrable (fun y => f (z.re + y * I)) volume z.im 0 ∧
        IntervalIntegrable (fun y => f (z.re + y * I)) volume 0 w.im := by
      constructor
      · exact intervalIntegrable_of_continuousOn_rect z w f z.re left_mem_uIcc z.im 0
          left_mem_uIcc h0 h_cont_rect
      · exact intervalIntegrable_of_continuousOn_rect z w f z.re left_mem_uIcc 0 w.im
          h0 right_mem_uIcc h_cont_rect
    have h_split := wedgeIntegral_split_y z w 0 f hf_int_w hf_int_z
    rw [h_split]
    have h1 : wedgeIntegral z (w.re + (0:ℝ) * I) f + wedgeIntegral (w.re + (0:ℝ) * I) z f = 0 := by
      apply wedgeIntegral_add_eq_zero_of_continuousOn_of_differentiableOn
      · apply h_cont_rect.mono
        intro v hv
        rw [Rectangle, mem_reProdIm] at hv ⊢
        simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, sub_zero, add_im, ofReal_im,
          mul_im, I_im, mul_one, add_zero] at hv
        refine ⟨hv.1, ?_⟩
        exact uIcc_subset_uIcc left_mem_uIcc h0 hv.2
      · simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, sub_zero, add_im, ofReal_im,
          mul_im, I_im, mul_one, add_zero]
        exact differentiableOn_split_y0 f (min z.re w.re) (max z.re w.re) z.im hf_ana_neg hf_ana_pos
    have h2 : wedgeIntegral (z.re + (0:ℝ) * I) w f + wedgeIntegral w (z.re + (0:ℝ) * I) f = 0 := by
      apply wedgeIntegral_add_eq_zero_of_continuousOn_of_differentiableOn
      · apply h_cont_rect.mono
        intro v hv
        rw [Rectangle, mem_reProdIm] at hv ⊢
        simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, sub_zero, add_im, ofReal_im,
          mul_im, I_im, mul_one, add_zero] at hv
        refine ⟨hv.1, ?_⟩
        exact uIcc_subset_uIcc h0 right_mem_uIcc hv.2
      · simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, sub_zero, add_im, ofReal_im,
          mul_im, I_im, mul_one, add_zero, min_comm 0 w.im, max_comm 0 w.im]
        exact differentiableOn_split_y0 f (min z.re w.re) (max z.re w.re) w.im hf_ana_neg hf_ana_pos
    rw [h1, h2, add_zero]
  · apply wedgeIntegral_add_eq_zero_of_continuousOn_of_differentiableOn f z w h_cont_rect
    rcases lt_trichotomy 0 z.im with h | h | h
    · have hw_im : 0 < w.im := by
        by_contra h_contra
        push Not at h_contra
        have h_in : (0:ℝ) ∈ uIcc z.im w.im := by
          rw [mem_uIcc]
          exact Or.inr ⟨h_contra, h.le⟩
        exact h0 h_in
      have h_sub : Ioo (min z.im w.im) (max z.im w.im) ⊆ Ioi 0 := by
        intro t ht
        exact lt_trans (lt_min h hw_im) ht.1
      have h_sub2 :
          Ioo (min z.re w.re) (max z.re w.re) ×ℂ Ioo (min z.im w.im) (max z.im w.im) ⊆
            upperHalfPlane := by
        intro v hv; rw [mem_reProdIm] at hv; exact h_sub hv.2
      exact hf_ana_pos.differentiableOn.mono h_sub2
    · rw [← h] at h0
      have h_in : (0:ℝ) ∈ uIcc 0 w.im := left_mem_uIcc
      exact False.elim (h0 h_in)
    · have hw_im : w.im < 0 := by
        by_contra h_contra
        push Not at h_contra
        have h_in : (0:ℝ) ∈ uIcc z.im w.im := by
          rw [mem_uIcc]
          exact Or.inl ⟨h.le, h_contra⟩
        exact h0 h_in
      have h_sub : Ioo (min z.im w.im) (max z.im w.im) ⊆ Iio 0 := by
        intro t ht
        exact lt_trans ht.2 (max_lt h hw_im)
      have h_sub2 :
          Ioo (min z.re w.re) (max z.re w.re) ×ℂ Ioo (min z.im w.im) (max z.im w.im) ⊆
            lowerHalfPlane := by
        intro v hv; rw [mem_reProdIm] at hv; exact h_sub hv.2
      exact hf_ana_neg.differentiableOn.mono h_sub2

theorem eow_1d_continuous (S : Set ℝ) (hS : IsOpen S) (f : ℂ → ℂ)
    (hf_cont : ContinuousOn f (slitDomain S))
    (hf_ana_pos : AnalyticOn ℂ f upperHalfPlane)
    (hf_ana_neg : AnalyticOn ℂ f lowerHalfPlane) :
    AnalyticOn ℂ f (slitDomain S) := by
  apply DifferentiableOn.analyticOn _ (isOpen_slitDomain hS)
  apply (isConservativeOn_and_continuousOn_iff_isDifferentiableOn (isOpen_slitDomain hS)).mp
  constructor
  · exact isConservativeOn_slitDomain S hS f hf_cont hf_ana_pos hf_ana_neg
  · exact hf_cont

lemma complex_algebra_lemma_aux (Z I_c F W : ℂ) :
    (Z * I_c) * (W * W * F) = (Z * W) * (I_c * W) * F := by
  ring

lemma complex_algebra_lemma (Z I_c F : ℂ) (hZ : Z ≠ 0) :
    (Z * I_c) * ((1 / Z ^ 2) * F) = (I_c / Z) * F := by
  have hz2 : Z ^ 2 = Z * Z := sq Z
  rw [hz2]
  calc
    (Z * I_c) * ((1 / (Z * Z)) * F) = (Z * I_c) * ((Z * Z)⁻¹ * F) := by rw [one_div]
    _ = (Z * I_c) * ((Z⁻¹ * Z⁻¹) * F) := by rw [mul_inv_rev, mul_comm Z⁻¹ Z⁻¹]
    _ = (Z * Z⁻¹) * (I_c * Z⁻¹) * F := by rw [complex_algebra_lemma_aux Z I_c F Z⁻¹]
    _ = 1 * (I_c * Z⁻¹) * F := by rw [mul_inv_cancel₀ hZ]
    _ = (I_c / Z) * F := by rw [one_mul, div_eq_mul_inv]

lemma integrand_eq (f : ℂ × ℂ → ℂ) (x y : ℂ) (R : ℝ) (hR : 0 < R) (θ : ℝ) :
    deriv (circleMap x R) θ • ((1 / (circleMap x R θ - x) ^ 2) * f (circleMap x R θ, y)) =
    (I / (R * exp (θ * I))) * f (x + R * exp (θ * I), y) := by
  rw [deriv_circleMap]
  rw [circleMap_sub_center]
  have h_c0 : circleMap 0 R θ = R * exp (θ * I) := by
    simp [circleMap]
  rw [h_c0]
  have h_cx : circleMap x R θ = x + R * exp (θ * I) := by
    simp [circleMap]
  rw [h_cx]
  change (↑R * exp (↑θ * I) * I) *
    ((1 / (↑R * exp (↑θ * I)) ^ 2) * f (x + ↑R * exp (↑θ * I), y)) = _
  have hZ : (R : ℂ) * exp (θ * I) ≠ 0 := mul_ne_zero (by exact_mod_cast hR.ne') (exp_ne_zero _)
  exact complex_algebra_lemma _ I _ hZ

lemma partial_deriv_eq_intervalIntegral
    (f : ℂ × ℂ → ℂ) (x y : ℂ) (R : ℝ) (hR : 0 < R)
    (h_diff : DifferentiableOn ℂ (fun w => f (w, y)) (Metric.closedBall x R)) :
    deriv (fun w => f (w, y)) x =
      (2 * ↑Real.pi * I)⁻¹ * ∫ θ in (0:ℝ)..(2 * Real.pi),
        (I / (R * exp (θ * I))) * f (x + R * exp (θ * I), y) := by
  have hc := DifferentiableOn.deriv_eq_smul_circleIntegral (E := ℂ)
    (f := fun w => f (w, y)) (c := x) (R := R) hR h_diff
  have hc2 : ∮ z in C(x, R), (1 / (z - x) ^ 2) * f (z, y) =
      (2 * ↑Real.pi * I) * deriv (fun w => f (w, y)) x := hc
  have hint := circleIntegral_def_Icc (fun w => (1 / (w - x) ^ 2) * f (w, y)) x R
  have h_eq_int : (∫ θ in (0:ℝ)..(2 * Real.pi),
        (I / (R * exp (θ * I))) * f (x + R * exp (θ * I), y)) =
      ∫ θ in Icc 0 (2 * Real.pi),
        deriv (circleMap x R) θ • ((1 / (circleMap x R θ - x) ^ 2) * f (circleMap x R θ, y)) := by
    rw [intervalIntegral.integral_of_le Real.two_pi_pos.le]
    rw [Measure.restrict_congr_set Ioc_ae_eq_Icc]
    congr 1
    ext θ
    exact (integrand_eq f x y R hR θ).symm
  rw [hint, ← h_eq_int] at hc2
  calc deriv (fun w => f (w, y)) x
    _ = (2 * ↑Real.pi * I)⁻¹ * ((2 * ↑Real.pi * I) * deriv (fun w => f (w, y)) x) := by
      rw [← mul_assoc, inv_mul_cancel₀, one_mul]
      exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_pos.ne')) I_ne_zero
    _ = (2 * ↑Real.pi * I)⁻¹ *
        ∫ θ in (0:ℝ)..(2 * Real.pi), (I / (↑R * exp (↑θ * I))) * f (x + ↑R * exp (↑θ * I), y) := by
      rw [← hc2]

lemma cont_aux (R : ℝ) (hR : 0 < R) (p₀ : ℂ × ℂ) (U : Set (ℂ × ℂ)) (f : ℂ × ℂ → ℂ)
    (h_cont : ContinuousOn f U)
    (h_in_U : ∀ p ∈ Metric.ball p₀ R, ∀ θ : ℝ, (p.1 + R * exp (θ * I), p.2) ∈ U) :
    Continuous (Function.uncurry (fun (p : Metric.ball p₀ R) (θ : ℝ) =>
      (I / (R * exp (θ * I))) * f (p.val.1 + R * exp (θ * I), p.val.2))) := by
  have h_left : Continuous (fun (X : Metric.ball p₀ R × ℝ) => I / (R * exp (X.2 * I))) := by
    apply Continuous.div continuous_const
    · exact continuous_const.mul
        (continuous_exp.comp (continuous_ofReal.comp continuous_snd |>.mul continuous_const))
    · intro X
      exact mul_ne_zero (by exact_mod_cast hR.ne') (exp_ne_zero _)
  have h_right :
      Continuous (fun (X : Metric.ball p₀ R × ℝ) =>
        f (X.1.val.1 + R * exp (X.2 * I), X.1.val.2)) := by
    have h_inner :
        Continuous (fun (X : Metric.ball p₀ R × ℝ) =>
          (X.1.val.1 + R * exp (X.2 * I), X.1.val.2)) := by
      have h1 : Continuous (fun X : Metric.ball p₀ R × ℝ => X.1.val.1) :=
        continuous_fst.comp (continuous_subtype_val.comp continuous_fst)
      have h2 : Continuous (fun X : Metric.ball p₀ R × ℝ => R * exp (X.2 * I)) :=
        continuous_const.mul
          (continuous_exp.comp (continuous_ofReal.comp continuous_snd |>.mul continuous_const))
      have h3 : Continuous (fun X : Metric.ball p₀ R × ℝ => X.1.val.2) :=
        continuous_snd.comp (continuous_subtype_val.comp continuous_fst)
      exact Continuous.prodMk (h1.add h2) h3
    apply ContinuousOn.comp_continuous h_cont h_inner
    intro X
    exact h_in_U X.1.val X.1.property X.2
  exact h_left.mul h_right

lemma continuousAt_partial_deriv_of_continuous_of_analytic
    {U : Set (ℂ × ℂ)} (hU : IsOpen U)
    (f : ℂ × ℂ → ℂ)
    (h_cont : ContinuousOn f U)
    (h_holo_x : ∀ (y : ℂ), DifferentiableOn ℂ (fun x => f (x, y)) {x | (x, y) ∈ U})
    (p₀ : ℂ × ℂ) (hp₀ : p₀ ∈ U) :
    ContinuousAt (fun p : ℂ × ℂ => deriv (fun x => f (x, p.2)) p.1) p₀ := by
  rcases Metric.isOpen_iff.mp hU p₀ hp₀ with ⟨ε, hε, h_ball⟩
  have hR : 0 < ε / 2 := half_pos hε
  set R := ε / 2
  have hR_le : ε / 2 ≤ ε := by linarith
  have h_subset : Metric.ball p₀ (2 * R) ⊆ U := by
    have h2R : 2 * R = ε := mul_div_cancel₀ ε two_ne_zero
    rw [h2R]
    exact h_ball
  have h_in_U : ∀ p ∈ Metric.ball p₀ R, ∀ θ : ℝ, (p.1 + R * exp (θ * I), p.2) ∈ U := by
    intro p hp θ
    apply h_subset
    rw [Metric.mem_ball] at hp ⊢
    have hp1 : dist p.1 p₀.1 ≤ dist p p₀ := le_max_left _ _
    have hp2 : dist p.2 p₀.2 ≤ dist p p₀ := le_max_right _ _
    have h1 : dist p.1 p₀.1 < R := lt_of_le_of_lt hp1 hp
    have h2 : dist p.2 p₀.2 < R := lt_of_le_of_lt hp2 hp
    have h2_lt : dist p.2 p₀.2 < 2 * R := lt_trans h2 (by linarith)
    have hd1 : dist (p.1 + R * exp (θ * I)) p₀.1 ≤
        dist (p.1 + R * exp (θ * I)) p.1 + dist p.1 p₀.1 :=
      dist_triangle _ _ _
    have h_circle : dist (p.1 + R * exp (θ * I)) p.1 = R := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_mul, norm_real, Real.norm_of_nonneg (le_of_lt hR),
        Complex.norm_exp_ofReal_mul_I, mul_one]
    have hd1_val : dist (p.1 + R * exp (θ * I)) p₀.1 < 2 * R := by linarith
    exact max_lt hd1_val h2_lt
  let f_int (p : Metric.ball p₀ R) (θ : ℝ) : ℂ :=
    (I / (R * exp (θ * I))) * f (p.val.1 + R * exp (θ * I), p.val.2)
  have h_cont_int : Continuous (Function.uncurry f_int) :=
    cont_aux R hR p₀ U f h_cont h_in_U
  let F_int (p : ℂ × ℂ) : ℂ :=
    ∫ θ in (0:ℝ)..(2 * Real.pi), (I / (R * exp (θ * I))) * f (p.1 + R * exp (θ * I), p.2)
  have h_int_cont : Continuous (fun (p : Metric.ball p₀ R) => F_int p.val) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      h_cont_int 0 (2 * Real.pi)
  have h_int_contOn : ContinuousOn F_int (Metric.ball p₀ R) :=
    continuousOn_iff_continuous_restrict.mpr h_int_cont
  have hp₀_nhds : Metric.ball p₀ R ∈ 𝓝 p₀ := Metric.ball_mem_nhds p₀ hR
  have h_int_contAt : ContinuousAt F_int p₀ :=
    ContinuousOn.continuousAt h_int_contOn hp₀_nhds
  have h_mul : ContinuousAt (fun p => (2 * ↑Real.pi * I)⁻¹ * F_int p) p₀ :=
    ContinuousAt.mul continuousAt_const h_int_contAt
  apply ContinuousAt.congr h_mul
  rw [Filter.EventuallyEq, eventually_nhds_iff]
  refine ⟨Metric.ball p₀ R, ?_, Metric.isOpen_ball, Metric.mem_ball_self hR⟩
  intro p hp
  have h_diff_p : DifferentiableOn ℂ (fun w => f (w, p.2)) (Metric.closedBall p.1 R) := by
    apply DifferentiableOn.mono (h_holo_x p.2)
    intro w hw
    simp only [mem_setOf_eq]
    have hw_dist : dist w p.1 ≤ R := Metric.mem_closedBall.mp hw
    have hp_dist : dist p p₀ < R := Metric.mem_ball.mp hp
    have d1 : dist w p₀.1 ≤ dist w p.1 + dist p.1 p₀.1 := dist_triangle w p.1 p₀.1
    have h1 : dist p.1 p₀.1 ≤ dist p p₀ := by
      rw [Prod.dist_eq]
      exact le_max_left _ _
    have h2 : dist p.2 p₀.2 ≤ dist p p₀ := by
      rw [Prod.dist_eq]
      exact le_max_right _ _
    have d1_lt : dist w p₀.1 < 2 * R := by
      calc dist w p₀.1 ≤ dist w p.1 + dist p.1 p₀.1 := d1
        _ ≤ R + dist p p₀ := add_le_add hw_dist h1
        _ < R + R := by linarith
        _ = 2 * R := by ring
    have d2_lt : dist p.2 p₀.2 < 2 * R := by
      calc dist p.2 p₀.2 ≤ dist p p₀ := h2
        _ < R := hp_dist
        _ < 2 * R := by linarith
    have h_max : dist (w, p.2) p₀ < ε := by
      rw [Prod.dist_eq]
      have h_eq : 2 * R = ε := by
        change 2 * (ε / 2) = ε
        ring
      rw [← h_eq]
      exact max_lt d1_lt d2_lt
    exact h_ball h_max
  have heq := partial_deriv_eq_intervalIntegral f p.1 p.2 R hR h_diff_p
  exact heq.symm

lemma osgood_2d {U : Set (ℂ × ℂ)} (hU : IsOpen U)
    (f : ℂ × ℂ → ℂ)
    (h_cont : ContinuousOn f U)
    (h_holo_x : ∀ (y : ℂ), DifferentiableOn ℂ (fun x => f (x, y)) {x | (x, y) ∈ U})
    (h_holo_y : ∀ (x : ℂ), DifferentiableOn ℂ (fun y => f (x, y)) {y | (x, y) ∈ U}) :
    DifferentiableOn ℂ f U := by
  intro p hp
  let f₁ : ℂ → ℂ → ℂ →L[ℂ] ℂ := fun x y => (1 : ℂ →L[ℂ] ℂ).smulRight (deriv (fun w => f (w, y)) x)
  let f₂ : ℂ → ℂ → ℂ →L[ℂ] ℂ := fun x y => (1 : ℂ →L[ℂ] ℂ).smulRight (deriv (fun w => f (x, w)) y)
  have df₁ : ∀ᶠ v in 𝓝 p, HasFDerivAt (fun x => f (x, v.2)) (f₁ v.1 v.2) v.1 := by
    apply eventually_nhds_iff.mpr
    refine ⟨U, ?_, hU, hp⟩
    intro v hv
    have h_diff : DifferentiableWithinAt ℂ (fun x => f (x, v.2)) {x | (x, v.2) ∈ U} v.1 :=
      h_holo_x v.2 v.1 hv
    have hU_x : IsOpen {x | (x, v.2) ∈ U} :=
      hU.preimage (Continuous.prodMk continuous_id continuous_const)
    exact (h_diff.differentiableAt (hU_x.mem_nhds hv)).hasDerivAt.hasFDerivAt
  have df₂ : ∀ᶠ v in 𝓝 p, HasFDerivAt (fun y => f (v.1, y)) (f₂ v.1 v.2) v.2 := by
    apply eventually_nhds_iff.mpr
    refine ⟨U, ?_, hU, hp⟩
    intro v hv
    have h_diff : DifferentiableWithinAt ℂ (fun y => f (v.1, y)) {y | (v.1, y) ∈ U} v.2 :=
      h_holo_y v.1 v.2 hv
    have hU_y : IsOpen {y | (v.1, y) ∈ U} :=
      hU.preimage (Continuous.prodMk continuous_const continuous_id)
    exact (h_diff.differentiableAt (hU_y.mem_nhds hv)).hasDerivAt.hasFDerivAt
  have cf₁ : ContinuousAt ↿f₁ p := by
    have hc := continuousAt_partial_deriv_of_continuous_of_analytic hU f h_cont h_holo_x p hp
    have h_smul : Continuous (fun c : ℂ => (1 : ℂ →L[ℂ] ℂ).smulRight c) :=
      (ContinuousLinearMap.smulRightL ℂ ℂ ℂ (1 : ℂ →L[ℂ] ℂ)).continuous
    exact h_smul.continuousAt.comp hc
  have cf₂ : ContinuousAt ↿f₂ p := by
    let f_symm : ℂ × ℂ → ℂ := fun v => f (v.2, v.1)
    have hU_symm : IsOpen (Prod.swap ⁻¹' U) := hU.preimage continuous_swap
    have h_cont_symm : ContinuousOn f_symm (Prod.swap ⁻¹' U) :=
      h_cont.comp continuous_swap.continuousOn (fun _ hx => hx)
    have hc := continuousAt_partial_deriv_of_continuous_of_analytic hU_symm f_symm h_cont_symm
      (fun x => h_holo_y x) p.swap (by simp [hp])
    have hc2 : ContinuousAt (fun v : ℂ × ℂ => deriv (fun w => f (v.1, w)) v.2) p :=
      hc.comp continuous_swap.continuousAt
    have h_smul : Continuous (fun c : ℂ => (1 : ℂ →L[ℂ] ℂ).smulRight c) :=
      (ContinuousLinearMap.smulRightL ℂ ℂ ℂ (1 : ℂ →L[ℂ] ℂ)).continuous
    exact h_smul.continuousAt.comp hc2
  have h_strict := hasStrictFDerivAt_uncurry_coprod (f := fun x y => f (x, y)) df₁ df₂ cf₁ cf₂
  exact h_strict.hasFDerivAt.differentiableAt.differentiableWithinAt

lemma continuous_coprod_C :
    Continuous (fun (w : (ℂ →L[ℂ] ℂ) × (ℂ →L[ℂ] ℂ)) => w.1.coprod w.2) := by
  fun_prop

lemma continuous_compRight_C (e : (Fin 2 → ℂ) →L[ℂ] ℂ × ℂ) :
    Continuous (fun (L : ℂ × ℂ →L[ℂ] ℂ) => L.comp e) := by
  have h : (fun (L : ℂ × ℂ →L[ℂ] ℂ) => L.comp e) =
      fun L => ContinuousLinearMap.compL ℂ (Fin 2 → ℂ) (ℂ × ℂ) ℂ L e := by
    ext L x
    rfl
  rw [h]
  fun_prop

noncomputable def partial_x (f' : ℂ × ℂ → ℂ) : ℂ → ℂ → ℂ →L[ℂ] ℂ :=
  fun x y => (1 : ℂ →L[ℂ] ℂ).smulRight (deriv (fun w => f' (w, y)) x)

noncomputable def partial_y (f' : ℂ × ℂ → ℂ) : ℂ → ℂ → ℂ →L[ℂ] ℂ :=
  fun x y => (1 : ℂ →L[ℂ] ℂ).smulRight (deriv (fun w => f' (x, w)) y)

lemma continuousOn_fderiv_of_differentiableOn_fin2_cf1 {U' : Set (ℂ × ℂ)} (hU' : IsOpen U')
    (f' : ℂ × ℂ → ℂ)
    (h_cont : ContinuousOn f' U')
    (h_holo_x : ∀ y, DifferentiableOn ℂ (fun x => f' (x, y)) {x | (x, y) ∈ U'}) :
    ContinuousOn ↿(partial_x f') U' := by
  intro p hp
  have hc := continuousAt_partial_deriv_of_continuous_of_analytic hU' f' h_cont h_holo_x p hp
  have h_smul : Continuous (fun c : ℂ => (1 : ℂ →L[ℂ] ℂ).smulRight c) :=
    (ContinuousLinearMap.smulRightL ℂ ℂ ℂ (1 : ℂ →L[ℂ] ℂ)).continuous
  exact (h_smul.continuousAt.comp hc).continuousWithinAt

lemma continuousOn_fderiv_of_differentiableOn_fin2_cf2 {U' : Set (ℂ × ℂ)} (hU' : IsOpen U')
    (f' : ℂ × ℂ → ℂ)
    (h_cont : ContinuousOn f' U')
    (h_holo_y : ∀ x, DifferentiableOn ℂ (fun y => f' (x, y)) {y | (x, y) ∈ U'}) :
    ContinuousOn ↿(partial_y f') U' := by
  intro p hp
  let f_symm : ℂ × ℂ → ℂ := fun v => f' (v.2, v.1)
  have hU_symm : IsOpen (Prod.swap ⁻¹' U') := hU'.preimage continuous_swap
  have h_cont_symm : ContinuousOn f_symm (Prod.swap ⁻¹' U') :=
    h_cont.comp continuous_swap.continuousOn (fun _ hx => hx)
  have hc := continuousAt_partial_deriv_of_continuous_of_analytic hU_symm f_symm h_cont_symm
    (fun x => h_holo_y x) p.swap (by simp [hp])
  have hc2 : ContinuousAt (fun v : ℂ × ℂ => deriv (fun w => f' (v.1, w)) v.2) p :=
    hc.comp continuous_swap.continuousAt
  have h_smul : Continuous (fun c : ℂ => (1 : ℂ →L[ℂ] ℂ).smulRight c) :=
    (ContinuousLinearMap.smulRightL ℂ ℂ ℂ (1 : ℂ →L[ℂ] ℂ)).continuous
  exact (h_smul.continuousAt.comp hc2).continuousWithinAt

lemma continuousOn_fderiv_of_differentiableOn_fin2_df1 {U' : Set (ℂ × ℂ)} (hU' : IsOpen U')
    (f' : ℂ × ℂ → ℂ)
    (h_holo_x : ∀ y, DifferentiableOn ℂ (fun x => f' (x, y)) {x | (x, y) ∈ U'}) :
    ∀ p ∈ U', HasFDerivAt (fun x => f' (x, p.2)) (partial_x f' p.1 p.2) p.1 := by
  intro p hp
  have hU_x : IsOpen {x | (x, p.2) ∈ U'} :=
    hU'.preimage (Continuous.prodMk continuous_id continuous_const)
  exact ((h_holo_x p.2 p.1 hp).differentiableAt (hU_x.mem_nhds hp)).hasDerivAt.hasFDerivAt

lemma continuousOn_fderiv_of_differentiableOn_fin2_df2 {U' : Set (ℂ × ℂ)} (hU' : IsOpen U')
    (f' : ℂ × ℂ → ℂ)
    (h_holo_y : ∀ x, DifferentiableOn ℂ (fun y => f' (x, y)) {y | (x, y) ∈ U'}) :
    ∀ p ∈ U', HasFDerivAt (fun y => f' (p.1, y)) (partial_y f' p.1 p.2) p.2 := by
  intro p hp
  have hU_y : IsOpen {y | (p.1, y) ∈ U'} :=
    hU'.preimage (Continuous.prodMk continuous_const continuous_id)
  exact ((h_holo_y p.1 p.2 hp).differentiableAt (hU_y.mem_nhds hp)).hasDerivAt.hasFDerivAt

lemma continuousOn_fderiv_of_differentiableOn_fin2_fderiv {U' : Set (ℂ × ℂ)} (hU' : IsOpen U')
    (f' : ℂ × ℂ → ℂ)
    (cf₁ : ContinuousOn ↿(partial_x f') U') (cf₂ : ContinuousOn ↿(partial_y f') U')
    (df₁ : ∀ p ∈ U', HasFDerivAt (fun x => f' (x, p.2)) (partial_x f' p.1 p.2) p.1)
    (df₂ : ∀ p ∈ U', HasFDerivAt (fun y => f' (p.1, y)) (partial_y f' p.1 p.2) p.2) :
    ∀ p ∈ U', fderiv ℂ f' p = (partial_x f' p.1 p.2).coprod (partial_y f' p.1 p.2) := by
  intro p hp
  have h_strict := hasStrictFDerivAt_uncurry_coprod (f := fun x y => f' (x, y))
    (by
      apply eventually_nhds_iff.mpr
      refine ⟨U', ?_, hU', hp⟩
      intro v hv
      exact df₁ v hv)
    (by
      apply eventually_nhds_iff.mpr
      refine ⟨U', ?_, hU', hp⟩
      intro v hv
      exact df₂ v hv)
    ((cf₁ p hp).continuousAt (hU'.mem_nhds hp))
    ((cf₂ p hp).continuousAt (hU'.mem_nhds hp))
  exact h_strict.hasFDerivAt.fderiv

lemma continuousOn_fderiv_of_differentiableOn_fin2_aux {U' : Set (ℂ × ℂ)} (hU' : IsOpen U')
    (f' : ℂ × ℂ → ℂ)
    (h_cont : ContinuousOn f' U')
    (h_holo_x : ∀ y, DifferentiableOn ℂ (fun x => f' (x, y)) {x | (x, y) ∈ U'})
    (h_holo_y : ∀ x, DifferentiableOn ℂ (fun y => f' (x, y)) {y | (x, y) ∈ U'}) :
    ContinuousOn (fderiv ℂ f') U' := by
  have cf₁ : ContinuousOn ↿(partial_x f') U' :=
    continuousOn_fderiv_of_differentiableOn_fin2_cf1 hU' f' h_cont h_holo_x
  have cf₂ : ContinuousOn ↿(partial_y f') U' :=
    continuousOn_fderiv_of_differentiableOn_fin2_cf2 hU' f' h_cont h_holo_y
  have df₁ : ∀ p ∈ U', HasFDerivAt (fun x => f' (x, p.2)) (partial_x f' p.1 p.2) p.1 :=
    continuousOn_fderiv_of_differentiableOn_fin2_df1 hU' f' h_holo_x
  have df₂ : ∀ p ∈ U', HasFDerivAt (fun y => f' (p.1, y)) (partial_y f' p.1 p.2) p.2 :=
    continuousOn_fderiv_of_differentiableOn_fin2_df2 hU' f' h_holo_y
  have h_fderiv' : ∀ p ∈ U', fderiv ℂ f' p = coprod (partial_x f' p.1 p.2) (partial_y f' p.1 p.2) :=
    continuousOn_fderiv_of_differentiableOn_fin2_fderiv hU' f' cf₁ cf₂ df₁ df₂
  have h_prod : ContinuousOn (fun p => (partial_x f' p.1 p.2, partial_y f' p.1 p.2)) U' :=
    ContinuousOn.prodMk cf₁ cf₂
  exact ContinuousOn.congr (continuous_coprod_C.comp_continuousOn h_prod) h_fderiv'

lemma continuousOn_fderiv_of_differentiableOn_fin2 {U : Set (Fin 2 → ℂ)} (hU : IsOpen U)
    (f : (Fin 2 → ℂ) → ℂ) (hf : DifferentiableOn ℂ f U) :
    ContinuousOn (fderiv ℂ f) U := by
  let e := ContinuousLinearEquiv.finTwoArrow ℂ ℂ
  let U' := e.symm ⁻¹' U
  have hU' : IsOpen U' := hU.preimage e.symm.continuous
  let f' : ℂ × ℂ → ℂ := f ∘ e.symm
  have h_cont : ContinuousOn f' U' :=
    ContinuousOn.comp hf.continuousOn e.symm.continuous.continuousOn (fun _ hx => hx)
  have h_holo_x : ∀ y, DifferentiableOn ℂ (fun x => f' (x, y)) {x | (x, y) ∈ U'} := by
    intro y x hx
    let g : ℂ → ℂ × ℂ := fun x' => (x', y)
    have hg_diff : Differentiable ℂ g := by fun_prop
    have hg_diff2 : Differentiable ℂ (fun x' => e.symm (g x')) := e.symm.differentiable.comp hg_diff
    have hg_diff_at : DifferentiableWithinAt ℂ (fun x' => e.symm (g x')) {x | (x, y) ∈ U'} x :=
      hg_diff2.differentiableAt.differentiableWithinAt
    exact (hf _ hx).comp x hg_diff_at (fun x' hx' => hx')
  have h_holo_y : ∀ x, DifferentiableOn ℂ (fun y => f' (x, y)) {y | (x, y) ∈ U'} := by
    intro x y hy
    let g : ℂ → ℂ × ℂ := fun y' => (x, y')
    have hg_diff : Differentiable ℂ g := by fun_prop
    have hg_diff2 : Differentiable ℂ (fun y' => e.symm (g y')) := e.symm.differentiable.comp hg_diff
    have hg_diff_at : DifferentiableWithinAt ℂ (fun y' => e.symm (g y')) {y | (x, y) ∈ U'} y :=
      hg_diff2.differentiableAt.differentiableWithinAt
    exact (hf _ hy).comp y hg_diff_at (fun y' hy' => hy')
  have h_cont_fderiv' :=
    continuousOn_fderiv_of_differentiableOn_fin2_aux hU' f' h_cont h_holo_x h_holo_y
  have h_fderiv :
      ∀ p ∈ U, fderiv ℂ f p = (fderiv ℂ f' (e p)).comp (e : (Fin 2 → ℂ) →L[ℂ] ℂ × ℂ) := by
    intro p hp
    have hp_U' : e p ∈ U' := by simpa [U'] using hp
    have hd_f'_aux : DifferentiableAt ℂ f (e.symm (e p)) := by
      have heq : e.symm (e p) = p := ContinuousLinearEquiv.symm_apply_apply e p
      rw [heq]
      exact hf.differentiableAt (hU.mem_nhds hp)
    have hd_f' : DifferentiableAt ℂ f' (e p) :=
      DifferentiableAt.comp (e p) hd_f'_aux e.symm.differentiableAt
    have h_fderiv_comp := fderiv_comp p hd_f' e.differentiableAt
    have h_eq_f : f = f' ∘ e := by
      ext x
      simp [f']
    rw [h_eq_f]
    rw [e.hasFDerivAt.fderiv] at h_fderiv_comp
    exact h_fderiv_comp
  have h_cont_comp :
      ContinuousOn (fun p => (fderiv ℂ f' (e p)).comp (e : (Fin 2 → ℂ) →L[ℂ] ℂ × ℂ)) U := by
    let F : (Fin 2 → ℂ) → ℂ × ℂ →L[ℂ] ℂ := fun p => fderiv ℂ f' (e p)
    have hF_cont : ContinuousOn F U :=
      h_cont_fderiv'.comp e.continuous.continuousOn (fun p hp => by simpa [U'] using hp)
    have step1 : ContinuousOn (fun p => (F p).comp (e : (Fin 2 → ℂ) →L[ℂ] ℂ × ℂ)) U :=
      (continuous_compRight_C e).comp_continuousOn hF_cont
    apply ContinuousOn.congr step1
    intro x hx
    rfl
  exact ContinuousOn.congr h_cont_comp h_fderiv

end Analysis

namespace QFT

variable {n : ℕ}
def IsCone (V : Set (Fin n → ℝ)) : Prop :=
  ∀ x ∈ V, ∀ c > 0, (fun i => c * x i) ∈ V

def DualCone (V : Set (Fin n → ℝ)) : Set (Fin n → ℝ) :=
  { y | ∀ x ∈ V, 0 ≤ ∑ i, x i * y i }

lemma isClosed_DualCone (V : Set (Fin n → ℝ)) : IsClosed (DualCone V) := by
  have h_eq : DualCone V = ⋂ x ∈ V, { y | 0 ≤ ∑ i, x i * y i } := by
    ext y
    simp only [DualCone, mem_setOf_eq, mem_iInter]
  rw [h_eq]
  apply isClosed_biInter
  intro x _
  apply IsClosed.preimage
  · apply continuous_finsetSum Finset.univ
    intro i _
    apply Continuous.mul continuous_const (continuous_apply i)
  · exact isClosed_Ici

lemma convex_DualCone (V : Set (Fin n → ℝ)) : Convex ℝ (DualCone V) := by
  intro y₁ hy₁ y₂ hy₂ a b ha hb hab
  simp only [DualCone, mem_setOf_eq] at *
  intro x hx
  have h1 := hy₁ x hx
  have h2 := hy₂ x hx
  have h_sum : (∑ i, x i * (a * y₁ i + b * y₂ i)) =
      a * (∑ i, x i * y₁ i) + b * (∑ i, x i * y₂ i) := by
    calc
      _ = ∑ i, (a * (x i * y₁ i) + b * (x i * y₂ i)) := by
        congr 1
        ext i
        ring
      _ = (∑ i, a * (x i * y₁ i)) + (∑ i, b * (x i * y₂ i)) := Finset.sum_add_distrib
      _ = a * (∑ i, x i * y₁ i) + b * (∑ i, x i * y₂ i) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum]
  have h_target : (a • y₁ + b • y₂) = fun i => a * y₁ i + b * y₂ i := rfl
  rw [h_target]
  rw [h_sum]
  apply add_nonneg
  · exact mul_nonneg ha h1
  · exact mul_nonneg hb h2

lemma isCone_DualCone (V : Set (Fin n → ℝ)) : IsCone (DualCone V) := by
  intro y hy c hc
  simp only [DualCone, mem_setOf_eq] at *
  intro x hx
  have h1 := hy x hx
  have h_sum : (∑ i, x i * (c * y i)) = c * (∑ i, x i * y i) := by
    calc
      _ = ∑ i, c * (x i * y i) := by
        congr 1
        ext i
        ring
      _ = c * (∑ i, x i * y i) := by rw [← Finset.mul_sum]
  rw [h_sum]
  exact mul_nonneg (le_of_lt hc) h1

def TubeDomain (V : Set (Fin n → ℝ)) : Set (Fin n → ℂ) :=
  { z | (fun i => (z i).im) ∈ V }

lemma isOpen_TubeDomain {V : Set (Fin n → ℝ)} (hV : IsOpen V) :
    IsOpen (TubeDomain V) := by
  have h_eq : TubeDomain V = (fun z : Fin n → ℂ => fun i => (z i).im) ⁻¹' V := by rfl
  rw [h_eq]
  apply IsOpen.preimage
  · apply continuous_pi
    intro i
    exact Complex.continuous_im.comp (continuous_apply i)
  · exact hV

lemma convex_TubeDomain {V : Set (Fin n → ℝ)} (hV : Convex ℝ V) :
    Convex ℝ (TubeDomain V) := by
  intro z₁ hz₁ z₂ hz₂ a b ha hb hab
  simp only [TubeDomain, mem_setOf_eq] at *
  have h_im : (fun i => ((a • z₁ + b • z₂) i).im) =
      a • (fun i => (z₁ i).im) + b • (fun i => (z₂ i).im) := by
    ext i
    simp [Pi.add_apply, Pi.smul_apply, Complex.add_im]
  rw [h_im]
  exact hV hz₁ hz₂ ha hb hab

def WedgeDomain (V_plus V_minus U : Set (Fin n → ℝ)) : Set (Fin n → ℂ) :=
  TubeDomain V_plus ∪ TubeDomain V_minus ∪
    {z : Fin n → ℂ | (fun i => (z i).re) ∈ U ∧ (fun i => (z i).im) = 0}

def LocalTubeDomain (V U : Set (Fin n → ℝ)) (r : ℝ) : Set (Fin n → ℂ) :=
  { z | (fun i => (z i).re) ∈ U ∧ (fun i => (z i).im) ∈ V ∧ ‖(fun i => (z i).im)‖ < r }

def LocalWedgeDomain (V_plus V_minus U : Set (Fin n → ℝ)) (r : ℝ) : Set (Fin n → ℂ) :=
  LocalTubeDomain V_plus U r ∪ LocalTubeDomain V_minus U r ∪
    {z : Fin n → ℂ | (fun i => (z i).re) ∈ U ∧ (fun i => (z i).im) = 0}

lemma isOpen_LocalTubeDomain {V U : Set (Fin n → ℝ)} {r : ℝ} (hV : IsOpen V) (hU : IsOpen U) :
    IsOpen (LocalTubeDomain V U r) := by
  have h1 : Continuous (fun z : Fin n → ℂ => fun i => (z i).re) := by
    apply continuous_pi; intro i; exact Complex.continuous_re.comp (continuous_apply i)
  have h2 : Continuous (fun z : Fin n → ℂ => fun i => (z i).im) := by
    apply continuous_pi; intro i; exact Complex.continuous_im.comp (continuous_apply i)
  have h3 : Continuous (fun z : Fin n → ℂ => ‖fun i => (z i).im‖) :=
    continuous_norm.comp h2
  have eq : LocalTubeDomain V U r =
    ((fun z : Fin n → ℂ => fun i => (z i).re) ⁻¹' U) ∩
    ((fun z : Fin n → ℂ => fun i => (z i).im) ⁻¹' V) ∩
    ((fun z : Fin n → ℂ => ‖fun i => (z i).im‖) ⁻¹' (Set.Iio r)) := by
    ext z
    simp [LocalTubeDomain, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iio]
    tauto
  rw [eq]
  apply IsOpen.inter
  · apply IsOpen.inter
    · exact hU.preimage h1
    · exact hV.preimage h2
  · exact isOpen_Iio.preimage h3

def EpsteinTubeDomain (V_plus V_minus : Set (Fin n → ℝ)) : Set (Fin n → ℂ) :=
  TubeDomain (convexHull ℝ (V_plus ∪ V_minus))

lemma isOpen_EpsteinTubeDomain {V_plus V_minus : Set (Fin n → ℝ)}
    (hV_plus : IsOpen V_plus) (hV_minus : IsOpen V_minus) :
    IsOpen (EpsteinTubeDomain V_plus V_minus) := by
  apply isOpen_TubeDomain
  apply IsOpen.convexHull
  exact IsOpen.union hV_plus hV_minus

noncomputable def supportFunction (K : Set (Fin n → ℝ)) (y : Fin n → ℝ) : ℝ :=
  sSup { ∑ i, x i * y i | x ∈ K }

lemma bddAbove_inner_of_isCompact {K : Set (Fin n → ℝ)} (hK : IsCompact K) (y : Fin n → ℝ) :
    BddAbove { ∑ i, x i * y i | x ∈ K } := by
  have h_cont : Continuous (fun x : Fin n → ℝ => ∑ i, x i * y i) := by
    apply continuous_finsetSum Finset.univ
    intro i _
    exact Continuous.mul (continuous_apply i) continuous_const
  have h_comp : IsCompact ((fun x : Fin n → ℝ => ∑ i, x i * y i) '' K) := hK.image h_cont
  have h_bdd : BddAbove ((fun x : Fin n → ℝ => ∑ i, x i * y i) '' K) := h_comp.bddAbove
  have h_eq : ((fun x : Fin n → ℝ => ∑ i, x i * y i) '' K) = { ∑ i, x i * y i | x ∈ K } := by
    ext r
    simp only [mem_image, mem_setOf_eq]
  rw [← h_eq]
  exact h_bdd

lemma supportFunction_nonpos_of_subset_dualCone
    {V K : Set (Fin n → ℝ)} (hK : K ⊆ DualCone V) (y : Fin n → ℝ) (hy : y ∈ V) :
    supportFunction K (-y) ≤ 0 := by
  unfold supportFunction
  by_cases h_emp : K = ∅
  · simp [h_emp]
  · have h_nonempty : K.Nonempty := nonempty_iff_ne_empty.mpr h_emp
    apply csSup_le
    · rcases h_nonempty with ⟨x, hx⟩
      use (∑ i, x i * (-y) i)
      simp only [mem_setOf_eq]
      exact ⟨x, hx, rfl⟩
    · rintro _ ⟨x, hx, rfl⟩
      have hx_dual := hK hx
      simp only [DualCone, mem_setOf_eq] at hx_dual
      have h_nonneg := hx_dual y hy
      have h_eq : (∑ i, x i * (-y) i) = - (∑ i, y i * x i) := by
        calc
          (∑ i, x i * (-y) i) = ∑ i, -(x i * y i) := by simp [mul_neg]
          _ = - (∑ i, x i * y i) := by rw [Finset.sum_neg_distrib]
          _ = - (∑ i, y i * x i) := by simp [mul_comm]
      rw [h_eq]
      exact neg_nonpos.mpr h_nonneg

lemma tendsto_integral_boundary
    (V : Set (Fin n → ℝ))
    (f : (Fin n → ℝ) → (Fin n → ℝ) → ℂ)
    (g : (Fin n → ℝ) → ℂ)
    (bound : (Fin n → ℝ) → ℝ)
    (h_bound_integrable : Integrable bound volume)
    (h_f_meas : ∀ᶠ y in nhdsWithin 0 V, AEStronglyMeasurable (f y) volume)
    (h_bound : ∀ᶠ y in nhdsWithin 0 V, ∀ᵐ x ∂volume, ‖f y x‖ ≤ bound x)
    (h_tendsto : ∀ᵐ x ∂volume, Tendsto (fun y => f y x) (nhdsWithin 0 V) (nhds (g x))) :
    Tendsto (fun y => ∫ x, f y x) (nhdsWithin 0 V) (nhds (∫ x, g x)) := by
  exact tendsto_integral_filter_of_dominated_convergence bound
    h_f_meas h_bound h_bound_integrable h_tendsto

lemma differentiableOn_integral_of_dominated_measure_1d
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (U : Set ℂ) (hU : IsOpen U)
    (f : ℂ → α → ℂ)
    (f' : ℂ → α → ℂ →L[ℂ] ℂ)
    (bound : α → ℝ)
    (h_bound_integrable : Integrable bound μ)
    (h_f_meas : ∀ z ∈ U, AEStronglyMeasurable (f z) μ)
    (h_f_int : ∀ z ∈ U, Integrable (f z) μ)
    (h_f'_meas : ∀ z ∈ U, AEStronglyMeasurable (f' z) μ)
    (h_bound : ∀ᵐ x ∂μ, ∀ z ∈ U, ‖f' z x‖ ≤ bound x)
    (h_diff : ∀ᵐ x ∂μ, ∀ z ∈ U, HasFDerivAt (fun w => f w x) (f' z x) z) :
    DifferentiableOn ℂ (fun z => ∫ x, f z x ∂μ) U := by
  intro z₀ hz₀
  have hs : U ∈ nhds z₀ := hU.mem_nhds hz₀
  have hF_meas : ∀ᶠ z in nhds z₀, AEStronglyMeasurable (f z) μ :=
    eventually_of_mem hs h_f_meas
  have hF_int_z₀ : Integrable (f z₀) μ := h_f_int z₀ hz₀
  have hF'_meas_z₀ : AEStronglyMeasurable (f' z₀) μ := h_f'_meas z₀ hz₀
  have h_deriv := hasFDerivAt_integral_of_dominated_of_fderiv_le hs
    hF_meas hF_int_z₀ hF'_meas_z₀ h_bound h_bound_integrable h_diff
  exact h_deriv.differentiableAt.differentiableWithinAt

lemma differentiableOn_integral_of_dominated_measure_2d
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (U : Set (Fin 2 → ℂ)) (hU : IsOpen U)
    (f : (Fin 2 → ℂ) → α → ℂ)
    (f' : (Fin 2 → ℂ) → α → (Fin 2 → ℂ) →L[ℂ] ℂ)
    (bound : α → ℝ)
    (h_bound_integrable : Integrable bound μ)
    (h_f_meas : ∀ z ∈ U, AEStronglyMeasurable (f z) μ)
    (h_f_int : ∀ z ∈ U, Integrable (f z) μ)
    (h_f'_meas : ∀ z ∈ U, AEStronglyMeasurable (f' z) μ)
    (h_bound : ∀ᵐ x ∂μ, ∀ z ∈ U, ‖f' z x‖ ≤ bound x)
    (h_diff : ∀ᵐ x ∂μ, ∀ z ∈ U, HasFDerivAt (fun w => f w x) (f' z x) z) :
    DifferentiableOn ℂ (fun z => ∫ x, f z x ∂μ) U := by
  intro z₀ hz₀
  have hs : U ∈ nhds z₀ := hU.mem_nhds hz₀
  have hF_meas : ∀ᶠ z in nhds z₀, AEStronglyMeasurable (f z) μ :=
    eventually_of_mem hs h_f_meas
  have hF_int_z₀ : Integrable (f z₀) μ := h_f_int z₀ hz₀
  have hF'_meas_z₀ : AEStronglyMeasurable (f' z₀) μ := h_f'_meas z₀ hz₀
  have h_deriv := hasFDerivAt_integral_of_dominated_of_fderiv_le hs
    hF_meas hF_int_z₀ hF'_meas_z₀ h_bound h_bound_integrable h_diff
  exact h_deriv.differentiableAt.differentiableWithinAt

lemma differentiableOn_integral_of_dominated
    (U : Set ℂ) (hU : IsOpen U)
    (f : ℂ → (Fin n → ℝ) → ℂ)
    (f' : ℂ → (Fin n → ℝ) → ℂ)
    (bound : (Fin n → ℝ) → ℝ)
    (h_bound_integrable : Integrable bound volume)
    (h_f_meas : ∀ z ∈ U, AEStronglyMeasurable (f z) volume)
    (h_f_int : ∀ z ∈ U, Integrable (f z) volume)
    (h_f'_meas : ∀ z ∈ U, AEStronglyMeasurable (f' z) volume)
    (h_bound : ∀ᵐ x ∂volume, ∀ z ∈ U, ‖f' z x‖ ≤ bound x)
    (h_diff : ∀ᵐ x ∂volume, ∀ z ∈ U, HasDerivAt (fun w => f w x) (f' z x) z) :
    DifferentiableOn ℂ (fun z => ∫ x, f z x) U := by
  intro z₀ hz₀
  have hs : U ∈ nhds z₀ := hU.mem_nhds hz₀
  have hF_meas : ∀ᶠ z in nhds z₀, AEStronglyMeasurable (f z) volume :=
    eventually_of_mem hs h_f_meas
  have hF_int_z₀ : Integrable (f z₀) volume := h_f_int z₀ hz₀
  have hF'_meas_z₀ : AEStronglyMeasurable (f' z₀) volume := h_f'_meas z₀ hz₀
  have h_deriv := hasDerivAt_integral_of_dominated_loc_of_deriv_le hs
    hF_meas hF_int_z₀ hF'_meas_z₀ h_bound h_bound_integrable h_diff
  exact h_deriv.2.differentiableAt.differentiableWithinAt

noncomputable def fourierLaplaceTransform
    (Ω : TopologicalSpace.Opens (Fin n → ℝ)) (φ : 𝓓(Ω, ℂ)) (z : Fin n → ℂ) : ℂ :=
  ∫ x : Fin n → ℝ, (φ x) * Complex.exp (-Complex.I * (∑ i, z i * (x i : ℂ)))

def ForwardCone (n : ℕ) : Set (Fin n → ℝ) :=
  {y | ∃ h : 0 < n, 0 < y ⟨0, h⟩ ∧
    (∑ i : Fin n, if i = ⟨0, h⟩ then (0 : ℝ) else (y i) ^ 2) < (y ⟨0, h⟩) ^ 2}

def slice_fun (f : (Fin n → ℂ) → ℂ) (x : Fin n → ℂ) (v : Fin n → ℝ) (w : ℂ) : ℂ :=
  f (fun i => x i + w * (v i : ℂ))

lemma slice_in_T_plus (V_plus : Set (Fin n → ℝ))
    (hV_plus_cone : ∀ v ∈ V_plus, ∀ (c : ℝ), c > 0 → (fun i => c * v i) ∈ V_plus)
    (x : Fin n → ℂ) (hx_real : ∀ i, (x i).im = 0)
    (v : Fin n → ℝ) (hv : v ∈ V_plus) (w : ℂ) (hw : w.im > 0) :
    (fun i => x i + w * (v i : ℂ)) ∈ TubeDomain V_plus := by
  have H : (fun i => (x i + w * (v i : ℂ)).im) = (fun i => w.im * v i) := by
    ext i
    simp [Complex.add_im, Complex.mul_im, hx_real i]
  change (fun i => (x i + w * (v i : ℂ)).im) ∈ V_plus
  rw [H]
  exact hV_plus_cone v hv w.im hw

lemma slice_in_T_minus (V_plus : Set (Fin n → ℝ))
    (hV_plus_cone : ∀ v ∈ V_plus, ∀ (c : ℝ), c > 0 → (fun i => c * v i) ∈ V_plus)
    (x : Fin n → ℂ) (hx_real : ∀ i, (x i).im = 0)
    (v : Fin n → ℝ) (hv : v ∈ V_plus) (w : ℂ) (hw : w.im < 0) :
    (fun i => x i + w * (v i : ℂ)) ∈ TubeDomain ((fun v : Fin n → ℝ => -v) '' V_plus) := by
  have H : (fun i => (x i + w * (v i : ℂ)).im) = (fun i => w.im * v i) := by
    ext i
    simp [Complex.add_im, Complex.mul_im, hx_real i]
  change (fun i => (x i + w * (v i : ℂ)).im) ∈ ((fun v : Fin n → ℝ => -v) '' V_plus)
  rw [H]
  have h_pos : -w.im > 0 := neg_pos.mpr hw
  have h_in_V : (fun i => -w.im * v i) ∈ V_plus := hV_plus_cone v hv (-w.im) h_pos
  have H2 : (fun i => w.im * v i) = (fun i => - (-w.im * v i)) := by
    ext i
    ring
  rw [H2]
  exact mem_image_of_mem (fun v => -v) h_in_V

def slice_real_set (U : Set (Fin n → ℝ)) (x : Fin n → ℂ) (v : Fin n → ℝ) : Set ℝ :=
  {w : ℝ | (fun i => (x i).re + w * v i) ∈ U}

lemma isOpen_slice_real_set
    (U : Set (Fin n → ℝ)) (hU_open : IsOpen U) (x : Fin n → ℂ) (v : Fin n → ℝ) :
    IsOpen (slice_real_set U x v) := by
  have h_cont : Continuous (fun w : ℝ => fun i => (x i).re + w * v i) := by
    apply continuous_pi
    intro i
    exact continuous_const.add (continuous_id.mul continuous_const)
  exact hU_open.preimage h_cont

lemma slice_in_wedge (V_plus U : Set (Fin n → ℝ))
    (hV_plus_cone : ∀ v ∈ V_plus, ∀ (c : ℝ), c > 0 → (fun i => c * v i) ∈ V_plus)
    (x : Fin n → ℂ) (hx_real : ∀ i, (x i).im = 0)
    (v : Fin n → ℝ) (hv : v ∈ V_plus) (w : ℂ)
    (hw : w ∈ Analysis.slitDomain (slice_real_set U x v)) :
    (fun i => x i + w * (v i : ℂ)) ∈
      WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U := by
  by_cases hw_im0 : w.im = 0
  · right
    dsimp [Analysis.slitDomain] at hw
    have hw_in : w.re ∈ slice_real_set U x v := by
      rcases hw with hw_ne | hw_in
      · exfalso; exact hw_ne hw_im0
      · exact hw_in
    have h_im : (fun i => (x i + w * (v i : ℂ)).im) = 0 := by
      ext i
      simp [Complex.add_im, Complex.mul_im, hx_real i, hw_im0]
    have h_re : (fun i => (x i + w * (v i : ℂ)).re) = (fun i => (x i).re + w.re * v i) := by
      ext i
      simp [Complex.add_re, Complex.mul_re, hw_im0]
    constructor
    · change (fun i => (x i + w * (v i : ℂ)).re) ∈ U
      rw [h_re]
      exact hw_in
    · change (fun i => (x i + w * (v i : ℂ)).im) = 0
      rw [h_im]
  · rcases lt_or_gt_of_ne hw_im0 with hw_neg | hw_pos
    · left; right; exact slice_in_T_minus V_plus hV_plus_cone x hx_real v hv w hw_neg
    · left; left; exact slice_in_T_plus V_plus hV_plus_cone x hx_real v hv w hw_pos

lemma slice_analytic (V_plus U : Set (Fin n → ℝ))
    (_hV_plus_open : IsOpen V_plus)
    (hV_plus_cone : ∀ v ∈ V_plus, ∀ (c : ℝ), c > 0 → (fun i => c * v i) ∈ V_plus)
    (hU_open : IsOpen U)
    (f : (Fin n → ℂ) → ℂ)
    (h_cont : ContinuousOn f (WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U))
    (h_holo_plus : DifferentiableOn ℂ f (TubeDomain V_plus))
    (h_holo_minus : DifferentiableOn ℂ f (TubeDomain ((fun v : Fin n → ℝ => -v) '' V_plus)))
    (x : Fin n → ℂ) (hx_real : ∀ i, (x i).im = 0) (_hx_U : (fun i => (x i).re) ∈ U)
    (v : Fin n → ℝ) (hv : v ∈ V_plus) :
    AnalyticOn ℂ (slice_fun f x v) (Analysis.slitDomain (slice_real_set U x v)) := by
  let slice_map := fun w : ℂ => (fun i => x i + w * (v i : ℂ))
  have h_slice_diff : Differentiable ℂ slice_map := by
    exact differentiable_pi.mpr (fun i => Differentiable.add
      ((differentiable_const (x i) : Differentiable ℂ (fun w : ℂ => x i)))
      (Differentiable.mul (differentiable_id : Differentiable ℂ (fun w : ℂ => w))
        ((differentiable_const (v i : ℂ) : Differentiable ℂ (fun w : ℂ => (v i : ℂ))))))
  have h_slice_cont : Continuous slice_map := h_slice_diff.continuous
  have hf_cont_slice :
      ContinuousOn (slice_fun f x v) (Analysis.slitDomain (slice_real_set U x v)) := by
    apply ContinuousOn.comp h_cont h_slice_cont.continuousOn
    intro w hw
    exact slice_in_wedge V_plus U hV_plus_cone x hx_real v hv w hw
  have h_isOpen_upper : IsOpen Analysis.upperHalfPlane := isOpen_lt continuous_const continuous_im
  have h_isOpen_lower : IsOpen Analysis.lowerHalfPlane := isOpen_lt continuous_im continuous_const
  have hf_ana_pos : AnalyticOn ℂ (slice_fun f x v) Analysis.upperHalfPlane := by
    have h_diff_on : DifferentiableOn ℂ (slice_fun f x v) Analysis.upperHalfPlane := by
      apply DifferentiableOn.comp h_holo_plus h_slice_diff.differentiableOn
      intro w hw
      exact slice_in_T_plus V_plus hV_plus_cone x hx_real v hv w hw
    exact DifferentiableOn.analyticOn h_diff_on h_isOpen_upper
  have hf_ana_neg : AnalyticOn ℂ (slice_fun f x v) Analysis.lowerHalfPlane := by
    have h_diff_on : DifferentiableOn ℂ (slice_fun f x v) Analysis.lowerHalfPlane := by
      apply DifferentiableOn.comp h_holo_minus h_slice_diff.differentiableOn
      intro w hw
      exact slice_in_T_minus V_plus hV_plus_cone x hx_real v hv w hw
    exact DifferentiableOn.analyticOn h_diff_on h_isOpen_lower
  exact Analysis.eow_1d_continuous (slice_real_set U x v)
    (isOpen_slice_real_set U hU_open x v) _ hf_cont_slice hf_ana_pos hf_ana_neg

lemma slice_analytic_at_zero (V_plus U : Set (Fin n → ℝ))
    (hV_plus_open : IsOpen V_plus)
    (hV_plus_cone : ∀ v ∈ V_plus, ∀ (c : ℝ), c > 0 → (fun i => c * v i) ∈ V_plus)
    (hU_open : IsOpen U)
    (f : (Fin n → ℂ) → ℂ)
    (h_cont : ContinuousOn f (WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U))
    (h_holo_plus : DifferentiableOn ℂ f (TubeDomain V_plus))
    (h_holo_minus : DifferentiableOn ℂ f (TubeDomain ((fun v : Fin n → ℝ => -v) '' V_plus)))
    (x : Fin n → ℝ) (hx_U : x ∈ U)
    (v : Fin n → ℝ) (hv : v ∈ V_plus) :
    AnalyticAt ℂ (slice_fun f (fun i => (x i : ℂ)) v) 0 := by
  let x_c : Fin n → ℂ := fun i => (x i : ℂ)
  have hx_real : ∀ i, (x_c i).im = 0 := fun i => by simp [x_c]
  have hx_re_U : (fun i => (x_c i).re) ∈ U := by
    have heq : (fun i => (x_c i).re) = x := by
      ext i
      simp [x_c]
    rw [heq]
    exact hx_U
  have h_ana := slice_analytic V_plus U hV_plus_open hV_plus_cone hU_open f h_cont
    h_holo_plus h_holo_minus x_c hx_real hx_re_U v hv
  have h0_in : (0 : ℂ) ∈ Analysis.slitDomain (slice_real_set U x_c v) := by
    simp only [Analysis.slitDomain, mem_setOf_eq, Complex.zero_im, ne_eq, not_true_eq_false,
      Complex.zero_re, false_or]
    simp only [slice_real_set, mem_setOf_eq]
    have heq : (fun i => (x_c i).re + 0 * v i) = (fun i => (x_c i).re) := by
      ext i
      ring
    rw [heq]
    exact hx_re_U
  have h_open : IsOpen (Analysis.slitDomain (slice_real_set U x_c v)) :=
    Analysis.isOpen_slitDomain (isOpen_slice_real_set U hU_open x_c v)
  exact h_ana.analyticAt (h_open.mem_nhds h0_in)

noncomputable def eow_F_disc
    (f : (Fin n → ℂ) → ℂ) (x : Fin n → ℂ) (v : Fin n → ℝ) (r : ℝ) (w : ℂ) : ℂ :=
  (2 * Real.pi * I)⁻¹ • ∮ z in C(0, r), (z - w)⁻¹ • (slice_fun f x v z)

lemma eow_F_disc_eq_slice_fun (f : (Fin n → ℂ) → ℂ) (x : Fin n → ℂ) (v : Fin n → ℝ)
    (r : ℝ) (_hr : 0 < r)
    (h_diff : DifferentiableOn ℂ (slice_fun f x v) (Metric.closedBall 0 r))
    (w : ℂ) (hw : norm w < r) :
    eow_F_disc f x v r w = slice_fun f x v w := by
  have hw_ball : w ∈ Metric.ball (0:ℂ) r := by simpa using hw
  rw [eow_F_disc]
  have h_eq := two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
    Set.countable_empty hw_ball h_diff.continuousOn (by
      intro z hz
      have h_nhds : Metric.closedBall (0:ℂ) r ∈ 𝓝 z :=
        Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hz.1) Metric.ball_subset_closedBall
      exact h_diff.differentiableAt h_nhds)
  exact h_eq

namespace Bochner
open Complex.HadamardThreeLines

def LShape (r R : ℝ) : Set (Fin 2 → ℝ) :=
  {x | (0 < x 0 ∧ x 0 < r ∧ 0 < x 1 ∧ x 1 < R) ∨ (0 < x 0 ∧ x 0 < R ∧ 0 < x 1 ∧ x 1 < r)}

def LShapeConvexHull (r R : ℝ) : Set (Fin 2 → ℝ) :=
  convexHull ℝ (LShape r R)

noncomputable def gaussianCutoff (ε : ℝ) (z : Fin 2 → ℂ) : ℂ :=
  Complex.exp (- (ε : ℂ) * (z 0 ^ 2 + z 1 ^ 2))

lemma gaussianCutoff_diff (ε : ℝ) :
    Differentiable ℂ (gaussianCutoff ε) := by
  apply Differentiable.comp
  · exact Complex.differentiable_exp
  · apply Differentiable.mul
    · exact differentiable_const _
    · apply Differentiable.add
      · apply Differentiable.pow
        exact differentiable_apply 0
      · apply Differentiable.pow
        exact differentiable_apply 1

noncomputable def f_eps (f : (Fin 2 → ℂ) → ℂ) (ε : ℝ) (z : Fin 2 → ℂ) : ℂ :=
  f z * gaussianCutoff ε z

noncomputable def fuks_cauchy_integral_joint
    (f : (Fin 2 → ℂ) → ℂ) (ε : ℝ) (y₂_star : ℝ) (z : Fin 2 → ℂ) : ℂ :=
  (2 * Real.pi * I)⁻¹ * ∫ t : ℝ,
    (f_eps f ε (fun i => if i = 0 then z 0 else (t : ℂ) + I * (y₂_star : ℂ))) /
      ((t : ℂ) + I * (y₂_star : ℂ) - z 1)

lemma fuks_cauchy_integral_diff_joint (f : (Fin 2 → ℂ) → ℂ) (ε : ℝ) (y₂_star : ℝ)
    (U : Set (Fin 2 → ℂ)) (hU_open : IsOpen U)
    (_hU_z2 : ∀ z ∈ U, (z 1).im ≠ y₂_star)
    (f_eps_deriv : (Fin 2 → ℂ) → ℝ → (Fin 2 → ℂ) →L[ℂ] ℂ)
    (bound : ℝ → ℝ)
    (h_bound_integrable : Integrable bound volume)
    (h_f_meas : ∀ z ∈ U, AEStronglyMeasurable (fun t : ℝ =>
      (f_eps f ε (fun i => if i = 0 then z 0 else (t : ℂ) + I * (y₂_star : ℂ))) /
        ((t : ℂ) + I * (y₂_star : ℂ) - z 1)) volume)
    (h_f_int : ∀ z ∈ U, Integrable (fun t : ℝ =>
      (f_eps f ε (fun i => if i = 0 then z 0 else (t : ℂ) + I * (y₂_star : ℂ))) /
        ((t : ℂ) + I * (y₂_star : ℂ) - z 1)) volume)
    (h_f'_meas : ∀ z ∈ U, AEStronglyMeasurable (f_eps_deriv z) volume)
    (h_bound : ∀ᵐ t : ℝ ∂volume, ∀ z ∈ U, ‖f_eps_deriv z t‖ ≤ bound t)
    (h_diff : ∀ᵐ t : ℝ ∂volume, ∀ z ∈ U, HasFDerivAt (fun w =>
      (f_eps f ε (fun i => if i = 0 then w 0 else (t : ℂ) + I * (y₂_star : ℂ))) /
        ((t : ℂ) + I * (y₂_star : ℂ) - w 1)) (f_eps_deriv z t) z) :
    DifferentiableOn ℂ (fun z => fuks_cauchy_integral_joint f ε y₂_star z) U := by
  have h_diff_int : DifferentiableOn ℂ (fun z => ∫ t : ℝ,
      (f_eps f ε (fun i => if i = 0 then z 0 else (t : ℂ) + I * (y₂_star : ℂ))) /
        ((t : ℂ) + I * (y₂_star : ℂ) - z 1)) U := by
    apply differentiableOn_integral_of_dominated_measure_2d U hU_open _ f_eps_deriv bound
      h_bound_integrable h_f_meas h_f_int h_f'_meas h_bound h_diff
  exact DifferentiableOn.const_smul h_diff_int (2 * Real.pi * I)⁻¹

lemma isOpen_LShape (r R : ℝ) : IsOpen (LShape r R) := by
  have h1 : IsOpen {x : Fin 2 → ℝ | 0 < x 0 ∧ x 0 < r ∧ 0 < x 1 ∧ x 1 < R} := by
    have h_0_pos : IsOpen {x : Fin 2 → ℝ | 0 < x 0} :=
      isOpen_lt continuous_const (continuous_apply 0)
    have h_0_lt_r : IsOpen {x : Fin 2 → ℝ | x 0 < r} :=
      isOpen_lt (continuous_apply 0) continuous_const
    have h_1_pos : IsOpen {x : Fin 2 → ℝ | 0 < x 1} :=
      isOpen_lt continuous_const (continuous_apply 1)
    have h_1_lt_R : IsOpen {x : Fin 2 → ℝ | x 1 < R} :=
      isOpen_lt (continuous_apply 1) continuous_const
    exact h_0_pos.inter (h_0_lt_r.inter (h_1_pos.inter h_1_lt_R))
  have h2 : IsOpen {x : Fin 2 → ℝ | 0 < x 0 ∧ x 0 < R ∧ 0 < x 1 ∧ x 1 < r} := by
    have h_0_pos : IsOpen {x : Fin 2 → ℝ | 0 < x 0} :=
      isOpen_lt continuous_const (continuous_apply 0)
    have h_0_lt_R : IsOpen {x : Fin 2 → ℝ | x 0 < R} :=
      isOpen_lt (continuous_apply 0) continuous_const
    have h_1_pos : IsOpen {x : Fin 2 → ℝ | 0 < x 1} :=
      isOpen_lt continuous_const (continuous_apply 1)
    have h_1_lt_r : IsOpen {x : Fin 2 → ℝ | x 1 < r} :=
      isOpen_lt (continuous_apply 1) continuous_const
    exact h_0_pos.inter (h_0_lt_R.inter (h_1_pos.inter h_1_lt_r))
  have h_eq : LShape r R =
      {x : Fin 2 → ℝ | 0 < x 0 ∧ x 0 < r ∧ 0 < x 1 ∧ x 1 < R} ∪
      {x : Fin 2 → ℝ | 0 < x 0 ∧ x 0 < R ∧ 0 < x 1 ∧ x 1 < r} := by
    ext x
    simp only [LShape, mem_setOf_eq, mem_union]
  rw [h_eq]
  exact h1.union h2

lemma isOpen_LShapeConvexHull (r R : ℝ) : IsOpen (LShapeConvexHull r R) :=
  (isOpen_LShape r R).convexHull

lemma fin2_cases (i : Fin 2) : i = 0 ∨ i = 1 := by
  match i with
  | ⟨0, _⟩ => exact Or.inl rfl
  | ⟨1, _⟩ => exact Or.inr rfl

lemma kajiwara_slice_differentiableAt (r R : ℝ) (f : (Fin 2 → ℂ) → ℂ)
    (hf_holo : DifferentiableOn ℂ f (TubeDomain (LShape r R)))
    (z₁ z₂ : ℂ) (hz : (fun i => if i = 0 then z₁ else z₂) ∈ TubeDomain (LShape r R)) :
    DifferentiableAt ℂ (fun z => f (fun i => if i = 0 then z₁ else z)) z₂ := by
  let g : ℂ → (Fin 2 → ℂ) := fun z => (fun i => if i = 0 then z₁ else z)
  have hg_diff : Differentiable ℂ g := by
    intro z
    apply differentiableAt_pi.mpr
    intro i
    dsimp [g]
    by_cases hi : i = 0
    · simp only [if_pos hi]
      exact differentiableAt_const z₁
    · simp only [if_neg hi]
      exact differentiableAt_id
  have h_isOpen : IsOpen (TubeDomain (LShape r R)) := isOpen_TubeDomain (isOpen_LShape r R)
  apply DifferentiableAt.comp z₂ (hf_holo.differentiableAt (h_isOpen.mem_nhds hz)) (hg_diff z₂)

lemma kajiwara_circle_in_tube (r R : ℝ) (_hr : 0 < r) (_hR : r < R)
    (w₁ : ℂ) (_hw₁ : 0 < w₁.im ∧ w₁.im < R)
    (ρ : ℝ) (hρ_pos : 0 < ρ) (hρ_lt_up : ρ < R - w₁.im) (hρ_lt_down : ρ < w₁.im)
    (θ : ℝ) (z₂ : ℂ) (hz₂ : 0 < z₂.im ∧ z₂.im < r) :
    (fun i => if i = 0 then circleMap w₁ ρ θ else z₂) ∈ TubeDomain (LShape r R) := by
  simp only [TubeDomain, LShape, mem_setOf_eq]
  right
  have h_im : (circleMap w₁ ρ θ).im = w₁.im + ρ * Real.sin θ := by
    simp [circleMap, Complex.add_im, Complex.mul_im, Complex.exp_im, Complex.exp_re]
  have h_sin_le : Real.sin θ ≤ 1 := Real.sin_le_one θ
  have h_sin_ge : -1 ≤ Real.sin θ := Real.neg_one_le_sin θ
  constructor
  · change 0 < (circleMap w₁ ρ θ).im; rw [h_im]; nlinarith
  · constructor
    · change (circleMap w₁ ρ θ).im < R; rw [h_im]; nlinarith
    · constructor
      · change 0 < z₂.im; exact hz₂.1
      · change z₂.im < r; exact hz₂.2

noncomputable def partialDeriv {n : ℕ} (f : (Fin n → ℂ) → ℂ) (j : Fin n) (z : Fin n → ℂ) : ℂ :=
  deriv (fun (w : ℂ) => f (Function.update z j w)) (z j)

lemma partialDeriv_eq_cauchy_integral {n : ℕ} {U : Set (Fin n → ℂ)} (_hU : IsOpen U)
    (f : (Fin n → ℂ) → ℂ) (hf : DifferentiableOn ℂ f U) (j : Fin n) (z₀ : Fin n → ℂ)
    (_hz₀ : z₀ ∈ U) (r : ℝ) (hr : 0 < r)
    (h_cball : Metric.closedBall (z₀ j) r ⊆ (fun w => Function.update z₀ j w) ⁻¹' U) :
    partialDeriv f j z₀ =
      (2 * Real.pi * I)⁻¹ * ∮ ζ in C(z₀ j, r), f (Function.update z₀ j ζ) / (ζ - z₀ j) ^ 2 := by
  let g : ℂ → ℂ := fun w => f (Function.update z₀ j w)
  have h_upd_diff : Differentiable ℂ (fun (w : ℂ) => Function.update z₀ j w) := by
    apply differentiable_pi.mpr
    intro i
    by_cases h : i = j
    · subst h
      have h_eq : (fun (w : ℂ) => Function.update z₀ i w i) = id := by ext w; simp
      rw [h_eq]
      exact differentiable_id
    · have h_eq : (fun (w : ℂ) => Function.update z₀ j w i) = fun w => z₀ i := by ext w; simp [h]
      rw [h_eq]
      exact differentiable_const _
  have hg_diff : DifferentiableOn ℂ g (Metric.closedBall (z₀ j) r) := by
    apply DifferentiableOn.comp hf (h_upd_diff.differentiableOn) h_cball
  have hc := DifferentiableOn.deriv_eq_smul_circleIntegral (E := ℂ)
    (f := g) (c := z₀ j) (R := r) hr hg_diff
  have hc2 : ∮ z in C(z₀ j, r), (1 / (z - z₀ j) ^ 2) * g z =
      (2 * ↑Real.pi * I) * deriv g (z₀ j) := hc
  have h_eq : (fun z => (1 / (z - z₀ j) ^ 2) * g z) = (fun z => g z / (z - z₀ j) ^ 2) := by
    ext z
    ring
  rw [h_eq] at hc2
  have h_mul : (2 * Real.pi * I : ℂ)⁻¹ * ∮ ζ in C(z₀ j, r), g ζ / (ζ - z₀ j) ^ 2 =
      (2 * Real.pi * I : ℂ)⁻¹ * ((2 * ↑Real.pi * I) * deriv g (z₀ j)) := by
    rw [hc2]
  rw [← mul_assoc] at h_mul
  have h_inv : (2 * Real.pi * I : ℂ)⁻¹ * (2 * Real.pi * I : ℂ) = 1 := by
    apply inv_mul_cancel₀
    simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, I_ne_zero, or_false]
    intro h
    rcases h with h_false | h_pi
    · exact h_false
    · have h2 : (Real.pi : ℂ).re = 0 := by rw [h_pi]; rfl
      have h3 : (Real.pi : ℂ).re = Real.pi := rfl
      rw [h3] at h2
      exact Real.pi_pos.ne' h2
  rw [h_inv, one_mul] at h_mul
  exact h_mul.symm

noncomputable def bochner_f_eps (f : (Fin 2 → ℂ) → ℂ) (ε : ℝ) (z : Fin 2 → ℂ) : ℂ :=
  f z * Complex.exp (-↑ε * (z 0 ^ 2 + z 1 ^ 2))

noncomputable def bochner_fourier_transform_eps
    (f : (Fin 2 → ℂ) → ℂ) (ε : ℝ) (y : Fin 2 → ℝ) (ξ : Fin 2 → ℝ) : ℂ :=
  ∫ (x : Fin 2 → ℝ), bochner_f_eps f ε (fun i => ↑(x i) + I * ↑(y i)) *
    Complex.exp (-I * (↑(x 0) * ↑(ξ 0) + ↑(x 1) * ↑(ξ 1)))

lemma fourier_shift_1d_eps_rect (a b ε M : ℝ) (hab : a ≤ b) (_hε : 0 < ε) (_hM : 0 < M)
    (g : ℂ → ℂ) (hg_holo : DifferentiableOn ℂ g {z | z.im ∈ Set.Icc a b}) :
    (((∫ (x : ℝ) in -M..M, g (↑x + ↑a * I)) - ∫ (x : ℝ) in -M..M, g (↑x + ↑b * I)) +
     I • ∫ (y : ℝ) in a..b, g (↑M + ↑y * I)) -
    I • ∫ (y : ℝ) in a..b, g (-↑M + ↑y * I) = 0 := by
  let z : ℂ := -↑M + ↑a * I
  let w : ℂ := ↑M + ↑b * I
  have h_z_re : z.re = -M := by simp [z]
  have h_w_re : w.re = M := by simp [w]
  have h_z_im : z.im = a := by simp [z]
  have h_w_im : w.im = b := by simp [w]
  have H := integral_boundary_rect_eq_zero_of_differentiableOn g z w
  have hd : DifferentiableOn ℂ g (uIcc z.re w.re ×ℂ uIcc z.im w.im) := by
    apply hg_holo.mono
    intro ζ hζ
    simp only [Set.mem_setOf_eq]
    have hζ_im : ζ.im ∈ uIcc z.im w.im := hζ.2
    rw [h_z_im, h_w_im] at hζ_im
    have : uIcc a b = Icc a b := uIcc_of_le hab
    rwa [this] at hζ_im
  have H2 := H hd
  rw [h_z_re, h_w_re, h_z_im, h_w_im] at H2
  have h_cast : (↑(-M) : ℂ) = -↑M := by push_cast; rfl
  rw [h_cast] at H2
  exact H2

lemma tendsto_exp_neg_mul_sq_atTop (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun M : ℝ => Real.exp (-ε * M ^ 2)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun M : ℝ => M ^ 2) atTop atTop := tendsto_pow_atTop (by norm_num)
  have h2 : Tendsto (fun M : ℝ => ε * M ^ 2) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hε h1
  have h3 : Tendsto (fun M : ℝ => -ε * M ^ 2) atTop atBot := by
    have : (fun M : ℝ => -ε * M ^ 2) = (fun x => -x) ∘ (fun M : ℝ => ε * M ^ 2) := by
      ext M
      dsimp
      ring
    rw [this]
    exact tendsto_neg_atTop_atBot.comp h2
  exact Real.tendsto_exp_atBot.comp h3

lemma vertical_integral_tendsto_zero (a b ε C : ℝ) (hab : a ≤ b) (hε : 0 < ε)
    (g : ℂ → ℂ)
    (hg_bound : ∀ z : ℂ, z.im ∈ Set.Icc a b → ‖g z‖ ≤ C * Real.exp (-ε * z.re ^ 2)) :
    Tendsto (fun M : ℝ => ∫ (y : ℝ) in a..b, g (↑M + ↑y * I)) atTop (𝓝 0) := by
  have h_bound_M : ∀ M : ℝ,
      ‖∫ (y : ℝ) in a..b, g (↑M + ↑y * I)‖ ≤ (C * Real.exp (-ε * M ^ 2)) * |b - a| := by
    intro M
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro y hy
    rw [uIoc_of_le hab] at hy
    have hy_Icc : y ∈ Icc a b := ⟨le_of_lt hy.1, hy.2⟩
    have hz_im : (↑M + ↑y * I : ℂ).im = y := by simp
    have hz_re : (↑M + ↑y * I : ℂ).re = M := by simp
    have hz_im_mem : (↑M + ↑y * I : ℂ).im ∈ Icc a b := by rwa [hz_im]
    have hg := hg_bound (↑M + ↑y * I) hz_im_mem
    rw [hz_re] at hg
    exact hg
  apply squeeze_zero_norm (h := h_bound_M)
  have h_lim := tendsto_exp_neg_mul_sq_atTop ε hε
  have h_mul := Tendsto.mul_const (|b - a|) (Tendsto.const_mul C h_lim)
  simp only [mul_zero, zero_mul] at h_mul
  exact h_mul

lemma vertical_integral_neg_tendsto_zero (a b ε C : ℝ) (hab : a ≤ b) (hε : 0 < ε)
    (g : ℂ → ℂ)
    (hg_bound : ∀ z : ℂ, z.im ∈ Set.Icc a b → ‖g z‖ ≤ C * Real.exp (-ε * z.re ^ 2)) :
    Tendsto (fun M : ℝ => ∫ (y : ℝ) in a..b, g (-↑M + ↑y * I)) atTop (𝓝 0) := by
  have h_bound_M : ∀ M : ℝ,
      ‖∫ (y : ℝ) in a..b, g (-↑M + ↑y * I)‖ ≤ (C * Real.exp (-ε * M ^ 2)) * |b - a| := by
    intro M
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro y hy
    rw [uIoc_of_le hab] at hy
    have hy_Icc : y ∈ Icc a b := ⟨le_of_lt hy.1, hy.2⟩
    have hz_im : (-↑M + ↑y * I : ℂ).im = y := by simp
    have hz_re : (-↑M + ↑y * I : ℂ).re = -M := by simp
    have hz_im_mem : (-↑M + ↑y * I : ℂ).im ∈ Icc a b := by rwa [hz_im]
    have hg := hg_bound (-↑M + ↑y * I) hz_im_mem
    rw [hz_re] at hg
    have : (-M) ^ 2 = M ^ 2 := neg_sq M
    rw [this] at hg
    exact hg
  apply squeeze_zero_norm (h := h_bound_M)
  have h_lim := tendsto_exp_neg_mul_sq_atTop ε hε
  have h_mul := Tendsto.mul_const (|b - a|) (Tendsto.const_mul C h_lim)
  simp only [mul_zero, zero_mul] at h_mul
  exact h_mul

lemma integrable_of_gaussian_bound (ε C : ℝ) (hε : 0 < ε) (y : ℝ) (a b : ℝ) (hy : y ∈ Icc a b)
    (g : ℂ → ℂ) (hg_holo : DifferentiableOn ℂ g {z | z.im ∈ Set.Icc a b})
    (hg_bound : ∀ z : ℂ, z.im ∈ Set.Icc a b → ‖g z‖ ≤ C * Real.exp (-ε * z.re ^ 2)) :
    Integrable (fun x : ℝ => g (↑x + I * ↑y)) := by
  have h_cont_path : Continuous (fun x : ℝ => (↑x + I * ↑y : ℂ)) := by continuity
  have h_map : ∀ x : ℝ, (↑x + I * ↑y : ℂ).im ∈ Icc a b := by
    intro x
    have : (↑x + I * ↑y : ℂ).im = y := by simp
    rwa [this]
  have hg_conton : ContinuousOn g {z | z.im ∈ Icc a b} := hg_holo.continuousOn
  have hg_cont : Continuous (fun x : ℝ => g (↑x + I * ↑y)) :=
    ContinuousOn.comp_continuous hg_conton h_cont_path (fun x => h_map x)
  have h_meas : AEStronglyMeasurable (fun x : ℝ => g (↑x + I * ↑y)) volume :=
    hg_cont.aestronglyMeasurable
  have h_gauss : Integrable (fun x : ℝ => C * Real.exp (-ε * x ^ 2)) volume :=
    (integrable_exp_neg_mul_sq hε).const_mul C
  apply Integrable.mono' h_gauss h_meas
  filter_upwards with x
  have h_re : (↑x + I * ↑y : ℂ).re = x := by simp
  have h_bound := hg_bound (↑x + I * ↑y) (h_map x)
  rwa [h_re] at h_bound

lemma fourier_shift_1d_eps (a b ε : ℝ) (hab : a < b) (hε : 0 < ε)
    (g : ℂ → ℂ) (hg_holo : DifferentiableOn ℂ g {z | z.im ∈ Set.Icc a b})
    (hg_bound : ∃ C : ℝ, ∀ z : ℂ, z.im ∈ Set.Icc a b → ‖g z‖ ≤ C * Real.exp (-ε * z.re ^ 2)) :
    ∫ (x : ℝ), g (↑x + I * ↑a) = ∫ (x : ℝ), g (↑x + I * ↑b) := by
  rcases hg_bound with ⟨C, hg_bound⟩
  have hab_le : a ≤ b := le_of_lt hab
  have ha_mem : a ∈ Icc a b := ⟨le_rfl, hab_le⟩
  have hb_mem : b ∈ Icc a b := ⟨hab_le, le_rfl⟩
  have hint_a := integrable_of_gaussian_bound ε C hε a a b ha_mem g hg_holo hg_bound
  have hint_b := integrable_of_gaussian_bound ε C hε b a b hb_mem g hg_holo hg_bound
  have h_comm_a : (fun x : ℝ => g (↑x + ↑a * I)) = (fun x : ℝ => g (↑x + I * ↑a)) := by
    ext x
    rw [mul_comm (a : ℂ) I]
  have h_comm_b : (fun x : ℝ => g (↑x + ↑b * I)) = (fun x : ℝ => g (↑x + I * ↑b)) := by
    ext x
    rw [mul_comm (b : ℂ) I]
  have h_tendsto_a :=
    MeasureTheory.intervalIntegral_tendsto_integral hint_a tendsto_neg_atTop_atBot tendsto_id
  have h_tendsto_b :=
    MeasureTheory.intervalIntegral_tendsto_integral hint_b tendsto_neg_atTop_atBot tendsto_id
  have h_tendsto_sub := h_tendsto_a.sub h_tendsto_b
  dsimp only [id] at h_tendsto_sub
  have h_rect_lim : Tendsto
      (fun M : ℝ => (∫ (x : ℝ) in -M..M, g (↑x + I * ↑a)) - (∫ (x : ℝ) in -M..M, g (↑x + I * ↑b)))
      atTop (𝓝 0) := by
    have h_v_pos := vertical_integral_tendsto_zero a b ε C hab_le hε g hg_bound
    have h_v_neg := vertical_integral_neg_tendsto_zero a b ε C hab_le hε g hg_bound
    have h_rhs : Tendsto (fun M : ℝ =>
        - (I • ∫ (y : ℝ) in a..b, g (↑M + ↑y * I)) + (I • ∫ (y : ℝ) in a..b, g (-↑M + ↑y * I)))
        atTop (𝓝 0) := by
      have h1 := (h_v_pos.const_smul I).neg
      have h2 := h_v_neg.const_smul I
      have h12 := h1.add h2
      simp only [smul_zero, neg_zero, zero_add] at h12
      exact h12
    apply Tendsto.congr' _ h_rhs
    filter_upwards [eventually_gt_atTop 0] with M hM
    have h_rect := fourier_shift_1d_eps_rect a b ε M hab_le hε hM g hg_holo
    rw [h_comm_a, h_comm_b] at h_rect
    have h_sub : (∫ (x : ℝ) in -M..M, g (↑x + I * ↑a)) - (∫ (x : ℝ) in -M..M, g (↑x + I * ↑b)) =
        - (I • ∫ (y : ℝ) in a..b, g (↑M + ↑y * I)) + (I • ∫ (y : ℝ) in a..b, g (-↑M + ↑y * I)) := by
      calc
        (∫ (x : ℝ) in -M..M, g (↑x + I * ↑a)) - (∫ (x : ℝ) in -M..M, g (↑x + I * ↑b))
        _ = (((∫ (x : ℝ) in -M..M, g (↑x + I * ↑a)) - (∫ (x : ℝ) in -M..M, g (↑x + I * ↑b)) +
              I • ∫ (y : ℝ) in a..b, g (↑M + ↑y * I)) -
             I • ∫ (y : ℝ) in a..b, g (-↑M + ↑y * I)) -
            (I • ∫ (y : ℝ) in a..b, g (↑M + ↑y * I)) +
            (I • ∫ (y : ℝ) in a..b, g (-↑M + ↑y * I)) := by ring
        _ = 0 - (I • ∫ (y : ℝ) in a..b, g (↑M + ↑y * I)) +
            (I • ∫ (y : ℝ) in a..b, g (-↑M + ↑y * I)) := by rw [h_rect]
        _ = - (I • ∫ (y : ℝ) in a..b, g (↑M + ↑y * I)) +
            (I • ∫ (y : ℝ) in a..b, g (-↑M + ↑y * I)) := by ring
    exact h_sub.symm
  have h_eq_zero : (∫ (x : ℝ), g (↑x + I * ↑a)) - (∫ (x : ℝ), g (↑x + I * ↑b)) = 0 :=
    tendsto_nhds_unique h_tendsto_sub h_rect_lim
  exact sub_eq_zero.mp h_eq_zero

lemma fourier_shift_1d_eps_uIcc (a b ε : ℝ) (hε : 0 < ε)
    (g : ℂ → ℂ) (hg_holo : DifferentiableOn ℂ g {z | z.im ∈ uIcc a b})
    (hg_bound : ∃ C : ℝ, ∀ z : ℂ, z.im ∈ uIcc a b → ‖g z‖ ≤ C * Real.exp (-ε * z.re ^ 2)) :
    ∫ (x : ℝ), g (↑x + I * ↑a) = ∫ (x : ℝ), g (↑x + I * ↑b) := by
  rcases lt_trichotomy a b with hab | rfl | hba
  · have h_uIcc : uIcc a b = Icc a b := uIcc_of_le (le_of_lt hab)
    rw [h_uIcc] at hg_holo hg_bound
    exact fourier_shift_1d_eps a b ε hab hε g hg_holo hg_bound
  · rfl
  · have h_uIcc : uIcc a b = Icc b a := uIcc_of_ge (le_of_lt hba)
    rw [h_uIcc] at hg_holo hg_bound
    have h_rev := fourier_shift_1d_eps b a ε hba hε g hg_holo hg_bound
    exact h_rev.symm

lemma exp_sub_I_mul_add (x y ξ : ℝ) :
    Complex.exp (-I * (↑x * ↑ξ)) * ↑(Real.exp (y * ξ)) =
    Complex.exp (-I * ((↑x + I * ↑y) * ↑ξ)) := by
  have h_exp_real : (↑(Real.exp (y * ξ)) : ℂ) = Complex.exp (↑(y * ξ)) := by
    exact ofReal_exp (y * ξ)
  rw [h_exp_real, ← Complex.exp_add]
  congr 1
  push_cast
  have h_I2 : I ^ 2 = -1 := I_sq
  linear_combination (↑ξ * ↑y) * h_I2

lemma exp_sub_I_mul_add_2d (x y ξ : Fin 2 → ℝ) :
    Complex.exp (-I * (↑(x 0) * ↑(ξ 0) + ↑(x 1) * ↑(ξ 1))) * ↑(Real.exp (y 0 * ξ 0 + y 1 * ξ 1)) =
    Complex.exp (-I * ((↑(x 0) + I * ↑(y 0)) * ↑(ξ 0) + (↑(x 1) + I * ↑(y 1)) * ↑(ξ 1))) := by
  have h_exp_real : (↑(Real.exp (y 0 * ξ 0 + y 1 * ξ 1)) : ℂ) =
      Complex.exp (↑(y 0 * ξ 0 + y 1 * ξ 1)) := by
    exact ofReal_exp (y 0 * ξ 0 + y 1 * ξ 1)
  rw [h_exp_real, ← Complex.exp_add]
  congr 1
  push_cast
  have h_I2 : I ^ 2 = -1 := I_sq
  linear_combination ((↑(ξ 0) * ↑(y 0) + ↑(ξ 1) * ↑(y 1))) * h_I2

noncomputable def bochner_integrand_F
    (f : (Fin 2 → ℂ) → ℂ) (ε : ℝ) (ξ : Fin 2 → ℝ) (z : Fin 2 → ℂ) : ℂ :=
  bochner_f_eps f ε z * Complex.exp (-I * (z 0 * ↑(ξ 0) + z 1 * ↑(ξ 1)))

lemma bochner_fourier_mul_exp_eq_integral (f : (Fin 2 → ℂ) → ℂ) (ε : ℝ) (y ξ : Fin 2 → ℝ) :
    bochner_fourier_transform_eps f ε y ξ * ↑(Real.exp (y 0 * ξ 0 + y 1 * ξ 1)) =
    ∫ (x : Fin 2 → ℝ), bochner_integrand_F f ε ξ (fun i => ↑(x i) + I * ↑(y i)) := by
  unfold bochner_fourier_transform_eps bochner_integrand_F
  rw [← MeasureTheory.integral_mul_const]
  congr 1
  ext x
  rw [mul_assoc]
  congr 1
  exact exp_sub_I_mul_add_2d x y ξ

lemma integral_finTwo_eq_integral_prod (g : (Fin 2 → ℝ) → ℂ) (hg : Integrable g) :
    ∫ (x : Fin 2 → ℝ), g x = ∫ (x₀ : ℝ), ∫ (x₁ : ℝ), g ![x₀, x₁] := by
  have h_pres := volume_preserving_finTwoArrow ℝ
  have H := h_pres.integral_comp' (fun p : ℝ × ℝ => g ![p.1, p.2])
  have h_comp : (fun x : Fin 2 → ℝ =>
      g ![(MeasurableEquiv.finTwoArrow x).1, (MeasurableEquiv.finTwoArrow x).2]) = g := by
    ext x
    rw [MeasurableEquiv.finTwoArrow_apply]
    congr 1
    ext i
    fin_cases i <;> rfl
  rw [h_comp] at H
  rw [H]
  have h_emb := (@MeasurableEquiv.finTwoArrow ℝ _).measurableEmbedding
  have h_int_iff := h_pres.integrable_comp_emb h_emb (g := fun p : ℝ × ℝ => g ![p.1, p.2])
  have h_comp_fun : (fun p : ℝ × ℝ => g ![p.1, p.2]) ∘ (⇑MeasurableEquiv.finTwoArrow) = g := by
    ext x
    exact congr_fun h_comp x
  rw [h_comp_fun] at h_int_iff
  have h_int_prod : Integrable (fun p : ℝ × ℝ => g ![p.1, p.2]) volume := h_int_iff.mp hg
  exact integral_prod (fun p : ℝ × ℝ => g ![p.1, p.2]) h_int_prod

lemma sq_add_I_mul_re (x y : ℝ) :
    ((↑x + I * ↑y : ℂ) ^ 2).re = x ^ 2 - y ^ 2 := by
  have : (↑x + I * ↑y : ℂ) ^ 2 = (↑x + I * ↑y) * (↑x + I * ↑y) := sq (↑x + I * ↑y)
  rw [this]
  simp
  ring

lemma neg_ofReal_mul_re (ε : ℝ) (w : ℂ) :
    (- (ε : ℂ) * w).re = -ε * w.re := by
  simp

lemma norm_exp_gaussian_decay (ε : ℝ) (x y : Fin 2 → ℝ) :
    ‖Complex.exp (-↑ε * ((↑(x 0) + I * ↑(y 0)) ^ 2 + (↑(x 1) + I * ↑(y 1)) ^ 2))‖ =
    Real.exp (-ε * (x 0 ^ 2 + x 1 ^ 2)) * Real.exp (ε * (y 0 ^ 2 + y 1 ^ 2)) := by
  rw [Complex.norm_exp]
  have h_re :
      ((- (ε : ℂ)) * (((x 0 : ℂ) + I * (y 0 : ℂ)) ^ 2 + ((x 1 : ℂ) + I * (y 1 : ℂ)) ^ 2)).re =
      -ε * (x 0 ^ 2 + x 1 ^ 2) + ε * (y 0 ^ 2 + y 1 ^ 2) := by
    rw [neg_ofReal_mul_re, add_re, sq_add_I_mul_re, sq_add_I_mul_re]
    ring
  rw [h_re, Real.exp_add]

lemma norm_exp_fourier (ξ : Fin 2 → ℝ) (x y : Fin 2 → ℝ) :
    ‖Complex.exp
      (-I * (((x 0 : ℂ) + I * (y 0 : ℂ)) * (ξ 0 : ℂ) + ((x 1 : ℂ) + I * (y 1 : ℂ)) * (ξ 1 : ℂ)))‖ =
    Real.exp (y 0 * ξ 0 + y 1 * ξ 1) := by
  rw [Complex.norm_exp]
  congr 1
  simp

lemma bochner_integrand_norm_eq (f : (Fin 2 → ℂ) → ℂ) (ε : ℝ) (ξ : Fin 2 → ℝ) (x y : Fin 2 → ℝ) :
    ‖bochner_integrand_F f ε ξ (fun i => ↑(x i) + I * ↑(y i))‖ =
    ‖f (fun i => ↑(x i) + I * ↑(y i))‖ * Real.exp (-ε * (x 0 ^ 2 + x 1 ^ 2)) *
    Real.exp (ε * (y 0 ^ 2 + y 1 ^ 2)) * Real.exp (y 0 * ξ 0 + y 1 * ξ 1) := by
  unfold bochner_integrand_F bochner_f_eps
  rw [norm_mul, norm_mul]
  have h_gauss := norm_exp_gaussian_decay ε x y
  have h_fourier := norm_exp_fourier ξ x y
  rw [h_gauss, h_fourier]
  ring

lemma integrable_gaussian_2d (ε : ℝ) (hε : 0 < ε) :
    Integrable (fun x : Fin 2 → ℝ => Real.exp (-ε * (x 0 ^ 2 + x 1 ^ 2))) := by
  have h_eq : (fun x : Fin 2 → ℝ => Real.exp (-ε * (x 0 ^ 2 + x 1 ^ 2))) =
      (fun p : ℝ × ℝ => Real.exp (-ε * p.1 ^ 2) * Real.exp (-ε * p.2 ^ 2)) ∘
      (⇑MeasurableEquiv.finTwoArrow) := by
    ext x
    simp only [Function.comp_apply, MeasurableEquiv.finTwoArrow_apply]
    rw [← Real.exp_add]
    congr 1
    ring
  rw [h_eq]
  have h_pres := volume_preserving_finTwoArrow ℝ
  have h_emb := (@MeasurableEquiv.finTwoArrow ℝ _).measurableEmbedding
  rw [h_pres.integrable_comp_emb h_emb]
  have h1 : Integrable (fun x : ℝ => Real.exp (-ε * x ^ 2)) volume := integrable_exp_neg_mul_sq hε
  have h_prod : Integrable
      (fun p : ℝ × ℝ => Real.exp (-ε * p.1 ^ 2) * Real.exp (-ε * p.2 ^ 2)) volume :=
    Integrable.mul_prod h1 h1
  exact h_prod

noncomputable def bochner_slice0
    (f : (Fin 2 → ℂ) → ℂ) (ε : ℝ) (ξ : Fin 2 → ℝ) (z₁ : ℂ) (w : ℂ) : ℂ :=
  bochner_integrand_F f ε ξ ![w, z₁]

lemma slice0_eq_integrand (f : (Fin 2 → ℂ) → ℂ) (ε : ℝ) (ξ : Fin 2 → ℝ) (x y : Fin 2 → ℝ) :
    bochner_slice0 f ε ξ (↑(x 1) + I * ↑(y 1)) (↑(x 0) + I * ↑(y 0)) =
    bochner_integrand_F f ε ξ (fun i => ↑(x i) + I * ↑(y i)) := by
  unfold bochner_slice0
  congr 1
  ext i
  fin_cases i <;> rfl

noncomputable def bochner_slice1
    (f : (Fin 2 → ℂ) → ℂ) (ε : ℝ) (ξ : Fin 2 → ℝ) (z₀ : ℂ) (w : ℂ) : ℂ :=
  bochner_integrand_F f ε ξ ![z₀, w]

lemma slice1_eq_integrand (f : (Fin 2 → ℂ) → ℂ) (ε : ℝ) (ξ : Fin 2 → ℝ) (x y : Fin 2 → ℝ) :
    bochner_slice1 f ε ξ (↑(x 0) + I * ↑(y 0)) (↑(x 1) + I * ↑(y 1)) =
    bochner_integrand_F f ε ξ (fun i => ↑(x i) + I * ↑(y i)) := by
  unfold bochner_slice1
  congr 1
  ext i
  fin_cases i <;> rfl

lemma mem_TubeDomain_pure_imag (V : Set (Fin 2 → ℝ)) (y : Fin 2 → ℝ) :
    (fun i => ↑(0 : ℝ) + I * ↑(y i)) ∈ TubeDomain V ↔ y ∈ V := by
  simp [TubeDomain]

lemma diff_affine_slice1 (z₀ : ℂ) :
    Differentiable ℂ (fun w : ℂ => (![z₀, w] : Fin 2 → ℂ)) := by
  apply differentiable_pi.mpr
  intro i
  fin_cases i
  · exact differentiable_const z₀
  · exact differentiable_id

lemma bochner_slice1_diffOn (r R : ℝ)
    (f : (Fin 2 → ℂ) → ℂ) (hf_holo : DifferentiableOn ℂ f (TubeDomain (LShape r R)))
    (ε : ℝ) (ξ : Fin 2 → ℝ) (x₀ y₀ y₁ y₁' : ℝ)
    (h_path : ∀ t ∈ uIcc y₁ y₁', ![y₀, t] ∈ LShape r R) :
    DifferentiableOn ℂ (fun w => bochner_integrand_F f ε ξ ![↑x₀ + I * ↑y₀, w])
      {w : ℂ | w.im ∈ uIcc y₁ y₁'} := by
  let z₀ : ℂ := ↑x₀ + I * ↑y₀
  have hz₀_im : z₀.im = y₀ := by simp [z₀]
  let L : ℂ → (Fin 2 → ℂ) := fun w => ![z₀, w]
  have hL_diff : Differentiable ℂ L := diff_affine_slice1 z₀
  have h_maps : MapsTo L {w : ℂ | w.im ∈ uIcc y₁ y₁'} (TubeDomain (LShape r R)) := by
    intro w hw
    simp only [mem_setOf_eq] at hw
    simp only [TubeDomain, mem_setOf_eq]
    have h_im : (fun i => (L w i).im) = ![y₀, w.im] := by
      ext i
      fin_cases i
      · simp [L, hz₀_im]
      · simp [L]
    rw [h_im]
    exact h_path w.im hw
  have hf_comp : DifferentiableOn ℂ (f ∘ L) {w : ℂ | w.im ∈ uIcc y₁ y₁'} :=
    hf_holo.comp hL_diff.differentiableOn h_maps
  have h_f_eps :
      DifferentiableOn ℂ (fun w => bochner_f_eps f ε (L w)) {w : ℂ | w.im ∈ uIcc y₁ y₁'} := by
    unfold bochner_f_eps
    apply DifferentiableOn.mul hf_comp
    have h_exp : Differentiable ℂ (fun w => Complex.exp (-↑ε * ((L w 0) ^ 2 + (L w 1) ^ 2))) := by
      apply Differentiable.comp Complex.differentiable_exp
      apply Differentiable.mul (differentiable_const _)
      apply Differentiable.add
      · exact (differentiable_pi.mp hL_diff 0).pow 2
      · exact (differentiable_pi.mp hL_diff 1).pow 2
    exact h_exp.differentiableOn
  unfold bochner_integrand_F
  apply DifferentiableOn.mul h_f_eps
  have h_fourier :
      Differentiable ℂ (fun w => Complex.exp (-I * (L w 0 * ↑(ξ 0) + L w 1 * ↑(ξ 1)))) := by
    apply Differentiable.comp Complex.differentiable_exp
    apply Differentiable.mul (differentiable_const _)
    apply Differentiable.add
    · exact (differentiable_pi.mp hL_diff 0).mul (differentiable_const _)
    · exact (differentiable_pi.mp hL_diff 1).mul (differentiable_const _)
  exact h_fourier.differentiableOn

lemma bound_on_uIcc (y₁ y₁' : ℝ) (t : ℝ) (ht : t ∈ uIcc y₁ y₁') :
    |t| ≤ max (|y₁|) (|y₁'|) := by
  rw [uIcc, mem_Icc] at ht
  have h1 : min y₁ y₁' ≤ t := ht.1
  have h2 : t ≤ max y₁ y₁' := ht.2
  have h_min_ge : - max (|y₁|) (|y₁'|) ≤ min y₁ y₁' := by
    rcases min_cases y₁ y₁' with ⟨hmin, _⟩ | ⟨hmin, _⟩
    · rw [hmin]
      have : -|y₁| ≤ y₁ := neg_abs_le y₁
      have : - max (|y₁|) (|y₁'|) ≤ -|y₁| := neg_le_neg (le_max_left _ _)
      linarith
    · rw [hmin]
      have : -|y₁'| ≤ y₁' := neg_abs_le y₁'
      have : - max (|y₁|) (|y₁'|) ≤ -|y₁'| := neg_le_neg (le_max_right _ _)
      linarith
  have h_max_le : max y₁ y₁' ≤ max (|y₁|) (|y₁'|) := by
    rcases max_cases y₁ y₁' with ⟨hmax, _⟩ | ⟨hmax, _⟩
    · rw [hmax]
      exact le_trans (le_abs_self y₁) (le_max_left _ _)
    · rw [hmax]
      exact le_trans (le_abs_self y₁') (le_max_right _ _)
  rw [abs_le]
  constructor
  · linarith
  · linarith

lemma sq_le_sq_of_bound (y₁ y₁' : ℝ) (t : ℝ) (ht : t ∈ uIcc y₁ y₁') :
    t ^ 2 ≤ (max (|y₁|) (|y₁'|)) ^ 2 := by
  have hb := bound_on_uIcc y₁ y₁' t ht
  have h_nonneg : 0 ≤ max (|y₁|) (|y₁'|) := le_max_of_le_left (abs_nonneg y₁)
  nlinarith [abs_le.mp hb]

lemma mul_le_mul_of_bound (y₁ y₁' ξ₁ : ℝ) (t : ℝ) (ht : t ∈ uIcc y₁ y₁') :
    t * ξ₁ ≤ max (|y₁|) (|y₁'|) * |ξ₁| := by
  have hb := bound_on_uIcc y₁ y₁' t ht
  have h1 : t * ξ₁ ≤ |t * ξ₁| := le_abs_self _
  rw [abs_mul] at h1
  have h2 : |t| * |ξ₁| ≤ max (|y₁|) (|y₁'|) * |ξ₁| := by
    exact mul_le_mul_of_nonneg_right hb (abs_nonneg _)
  exact le_trans h1 h2

lemma bochner_slice1_bound_const (f : (Fin 2 → ℂ) → ℂ)
    (hf_bound : ∃ M : ℝ, ∀ z : Fin 2 → ℂ, ‖f z‖ ≤ M)
    (ε : ℝ) (hε : 0 ≤ ε) (ξ : Fin 2 → ℝ) (x₀ y₀ y₁ y₁' : ℝ) :
    ∃ C : ℝ, ∀ w : ℂ, w.im ∈ uIcc y₁ y₁' →
      ‖bochner_integrand_F f ε ξ ![↑x₀ + I * ↑y₀, w]‖ ≤ C * Real.exp (-ε * w.re ^ 2) := by
  rcases hf_bound with ⟨M, hM⟩
  let K := max (|y₁|) (|y₁'|)
  let C := max M 0 * Real.exp (-ε * x₀ ^ 2) * Real.exp (ε * (y₀ ^ 2 + K ^ 2)) *
    Real.exp (y₀ * ξ 0 + K * |ξ 1|)
  use C
  intro w hw
  have h_rep : ![↑x₀ + I * ↑y₀, w] = fun i => ↑(![x₀, w.re] i) + I * ↑(![y₀, w.im] i) := by
    ext i
    fin_cases i
    · simp
    · simp [mul_comm I ↑w.im, Complex.re_add_im]
  rw [h_rep]
  rw [bochner_integrand_norm_eq]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have h_bound_f : ‖f (fun i => ↑(![x₀, w.re] i) + I * ↑(![y₀, w.im] i))‖ ≤ max M 0 :=
    le_trans (hM _) (le_max_left M 0)
  have h_gauss : Real.exp (-ε * (x₀ ^ 2 + w.re ^ 2)) =
      Real.exp (-ε * x₀ ^ 2) * Real.exp (-ε * w.re ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [h_gauss]
  have h_sq_le : w.im ^ 2 ≤ K ^ 2 := sq_le_sq_of_bound y₁ y₁' w.im hw
  have h_exp_y : Real.exp (ε * (y₀ ^ 2 + w.im ^ 2)) ≤ Real.exp (ε * (y₀ ^ 2 + K ^ 2)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have h_mul_le : w.im * ξ 1 ≤ K * |ξ 1| := mul_le_mul_of_bound y₁ y₁' (ξ 1) w.im hw
  have h_exp_xi : Real.exp (y₀ * ξ 0 + w.im * ξ 1) ≤ Real.exp (y₀ * ξ 0 + K * |ξ 1|) := by
    apply Real.exp_le_exp.mpr
    linarith
  have h_rew1 : ‖f (fun i => ↑(![x₀, w.re] i) + I * ↑(![y₀, w.im] i))‖ *
      (Real.exp (-ε * x₀ ^ 2) * Real.exp (-ε * w.re ^ 2)) *
      Real.exp (ε * (y₀ ^ 2 + w.im ^ 2)) * Real.exp (y₀ * ξ 0 + w.im * ξ 1) =
      (‖f (fun i => ↑(![x₀, w.re] i) + I * ↑(![y₀, w.im] i))‖ *
      Real.exp (-ε * x₀ ^ 2) *
      Real.exp (ε * (y₀ ^ 2 + w.im ^ 2)) * Real.exp (y₀ * ξ 0 + w.im * ξ 1)) *
      Real.exp (-ε * w.re ^ 2) := by ring
  rw [h_rew1]
  dsimp [C]
  have h_le_core : ‖f (fun i => ↑(![x₀, w.re] i) + I * ↑(![y₀, w.im] i))‖ *
      Real.exp (-ε * x₀ ^ 2) *
      Real.exp (ε * (y₀ ^ 2 + w.im ^ 2)) * Real.exp (y₀ * ξ 0 + w.im * ξ 1) ≤
      max M 0 * Real.exp (-ε * x₀ ^ 2) * Real.exp (ε * (y₀ ^ 2 + K ^ 2)) *
        Real.exp (y₀ * ξ 0 + K * |ξ 1|) := by
    have h1 : 0 ≤ Real.exp (-ε * x₀ ^ 2) := (Real.exp_pos _).le
    have h2 : 0 ≤ Real.exp (ε * (y₀ ^ 2 + w.im ^ 2)) := (Real.exp_pos _).le
    have h3 : 0 ≤ Real.exp (y₀ * ξ 0 + w.im * ξ 1) := (Real.exp_pos _).le
    gcongr
  exact mul_le_mul_of_nonneg_right h_le_core (Real.exp_pos _).le

lemma bochner_slice1_bound (_r _R : ℝ)
    (f : (Fin 2 → ℂ) → ℂ)
    (hf_bound : ∃ M : ℝ, ∀ z : Fin 2 → ℂ, ‖f z‖ ≤ M)
    (ε : ℝ) (hε : 0 < ε) (ξ : Fin 2 → ℝ) (x₀ y₀ y₁ y₁' : ℝ) :
    ∃ C : ℝ, ∀ w : ℂ, w.im ∈ uIcc y₁ y₁' →
      ‖bochner_integrand_F f ε ξ ![↑x₀ + I * ↑y₀, w]‖ ≤ C * Real.exp (-ε * w.re ^ 2) := by
  exact bochner_slice1_bound_const f hf_bound ε hε.le ξ x₀ y₀ y₁ y₁'

lemma bochner_integrand_integrable_of_bound (f : (Fin 2 → ℂ) → ℂ)
    (ε : ℝ) (hε : 0 < ε) (ξ : Fin 2 → ℝ) (y : Fin 2 → ℝ) (C : ℝ)
    (h_bound : ∀ (x : Fin 2 → ℝ), ‖bochner_integrand_F f ε ξ (fun i => ↑(x i) + I * ↑(y i))‖ ≤
      C * Real.exp (-ε * (x 0 ^ 2 + x 1 ^ 2)))
    (h_meas : AEStronglyMeasurable
      (fun x : Fin 2 → ℝ => bochner_integrand_F f ε ξ (fun i => ↑(x i) + I * ↑(y i))) volume) :
    Integrable (fun x : Fin 2 → ℝ => bochner_integrand_F f ε ξ (fun i => ↑(x i) + I * ↑(y i))) := by
  have h_int_gauss : Integrable (fun x : Fin 2 → ℝ => Real.exp (-ε * (x 0 ^ 2 + x 1 ^ 2))) :=
    integrable_gaussian_2d ε hε
  have h_int_g : Integrable (fun x : Fin 2 → ℝ => C * Real.exp (-ε * (x 0 ^ 2 + x 1 ^ 2))) :=
    h_int_gauss.const_mul C
  exact Integrable.mono' h_int_g h_meas (ae_of_all _ h_bound)

lemma bochner_integrand_bound_2d (f : (Fin 2 → ℂ) → ℂ)
    (hf_bound : ∃ M : ℝ, ∀ z : Fin 2 → ℂ, ‖f z‖ ≤ M)
    (ε : ℝ) (ξ : Fin 2 → ℝ) (y : Fin 2 → ℝ) :
    ∃ C : ℝ, ∀ (x : Fin 2 → ℝ), ‖bochner_integrand_F f ε ξ (fun i => ↑(x i) + I * ↑(y i))‖ ≤
      C * Real.exp (-ε * (x 0 ^ 2 + x 1 ^ 2)) := by
  rcases hf_bound with ⟨M, hM⟩
  let C := max M 0 * Real.exp (ε * (y 0 ^ 2 + y 1 ^ 2)) * Real.exp (y 0 * ξ 0 + y 1 * ξ 1)
  use C
  intro x
  rw [bochner_integrand_norm_eq]
  have hM_x : ‖f (fun i => ↑(x i) + I * ↑(y i))‖ ≤ max M 0 := le_trans (hM _) (le_max_left M 0)
  have h_exp_nonneg : 0 ≤ Real.exp (-ε * (x 0 ^ 2 + x 1 ^ 2)) := (Real.exp_pos _).le
  have h_exp_y_nonneg :
      0 ≤ Real.exp (ε * (y 0 ^ 2 + y 1 ^ 2)) * Real.exp (y 0 * ξ 0 + y 1 * ξ 1) := by positivity
  have h_rew : ‖f (fun i => ↑(x i) + I * ↑(y i))‖ * Real.exp (-ε * (x 0 ^ 2 + x 1 ^ 2)) *
    Real.exp (ε * (y 0 ^ 2 + y 1 ^ 2)) * Real.exp (y 0 * ξ 0 + y 1 * ξ 1) =
    (‖f (fun i => ↑(x i) + I * ↑(y i))‖ *
      (Real.exp (ε * (y 0 ^ 2 + y 1 ^ 2)) * Real.exp (y 0 * ξ 0 + y 1 * ξ 1))) *
      Real.exp (-ε * (x 0 ^ 2 + x 1 ^ 2)) := by ring
  rw [h_rew]
  dsimp [C]
  have h_c_rew : max M 0 * Real.exp (ε * (y 0 ^ 2 + y 1 ^ 2)) * Real.exp (y 0 * ξ 0 + y 1 * ξ 1) *
        Real.exp (-ε * (x 0 ^ 2 + x 1 ^ 2)) =
      (max M 0 * (Real.exp (ε * (y 0 ^ 2 + y 1 ^ 2)) * Real.exp (y 0 * ξ 0 + y 1 * ξ 1))) *
        Real.exp (-ε * (x 0 ^ 2 + x 1 ^ 2)) := by ring
  rw [h_c_rew]
  apply mul_le_mul_of_nonneg_right _ h_exp_nonneg
  apply mul_le_mul_of_nonneg_right hM_x h_exp_y_nonneg

lemma bochner_integrand_norm_le_gaussian (f : (Fin 2 → ℂ) → ℂ)
    (M : ℝ) (hM : ∀ z : Fin 2 → ℂ, ‖f z‖ ≤ M)
    (ε : ℝ) (ξ : Fin 2 → ℝ) (y : Fin 2 → ℝ) (x : Fin 2 → ℝ) :
    ‖bochner_integrand_F f ε ξ (fun i => ↑(x i) + I * ↑(y i))‖ ≤
      (max M 0 * Real.exp (ε * (y 0 ^ 2 + y 1 ^ 2)) * Real.exp (y 0 * ξ 0 + y 1 * ξ 1)) *
        Real.exp (-ε * (x 0 ^ 2 + x 1 ^ 2)) := by
  rw [bochner_integrand_norm_eq]
  have hM_x : ‖f (fun i => ↑(x i) + I * ↑(y i))‖ ≤ max M 0 := le_trans (hM _) (le_max_left M 0)
  have h_exp_nonneg : 0 ≤ Real.exp (-ε * (x 0 ^ 2 + x 1 ^ 2)) := (Real.exp_pos _).le
  have h_exp_y_nonneg :
      0 ≤ Real.exp (ε * (y 0 ^ 2 + y 1 ^ 2)) * Real.exp (y 0 * ξ 0 + y 1 * ξ 1) := by positivity
  have h_rew : ‖f (fun i => ↑(x i) + I * ↑(y i))‖ * Real.exp (-ε * (x 0 ^ 2 + x 1 ^ 2)) *
    Real.exp (ε * (y 0 ^ 2 + y 1 ^ 2)) * Real.exp (y 0 * ξ 0 + y 1 * ξ 1) =
    (‖f (fun i => ↑(x i) + I * ↑(y i))‖ *
      (Real.exp (ε * (y 0 ^ 2 + y 1 ^ 2)) * Real.exp (y 0 * ξ 0 + y 1 * ξ 1))) *
      Real.exp (-ε * (x 0 ^ 2 + x 1 ^ 2)) := by ring
  rw [h_rew]
  have h_c_rew : max M 0 * Real.exp (ε * (y 0 ^ 2 + y 1 ^ 2)) * Real.exp (y 0 * ξ 0 + y 1 * ξ 1) *
        Real.exp (-ε * (x 0 ^ 2 + x 1 ^ 2)) =
      (max M 0 * (Real.exp (ε * (y 0 ^ 2 + y 1 ^ 2)) * Real.exp (y 0 * ξ 0 + y 1 * ξ 1))) *
        Real.exp (-ε * (x 0 ^ 2 + x 1 ^ 2)) := by ring
  rw [h_c_rew]
  apply mul_le_mul_of_nonneg_right _ h_exp_nonneg
  apply mul_le_mul_of_nonneg_right hM_x h_exp_y_nonneg

lemma bochner_integrand_continuous_2d (f : (Fin 2 → ℂ) → ℂ) (ε : ℝ) (ξ : Fin 2 → ℝ) (y : Fin 2 → ℝ)
    (hf_cont : Continuous (fun x : Fin 2 → ℝ => f (fun i => ↑(x i) + I * ↑(y i)))) :
    Continuous (fun x : Fin 2 → ℝ => bochner_integrand_F f ε ξ (fun i => ↑(x i) + I * ↑(y i))) := by
  unfold bochner_integrand_F bochner_f_eps
  apply Continuous.mul
  · apply Continuous.mul hf_cont
    apply Continuous.comp Complex.continuous_exp
    apply Continuous.mul continuous_const
    apply Continuous.add
    · apply Continuous.pow
      exact (Complex.continuous_ofReal.comp (continuous_apply 0)).add continuous_const
    · apply Continuous.pow
      exact (Complex.continuous_ofReal.comp (continuous_apply 1)).add continuous_const
  · apply Continuous.comp Complex.continuous_exp
    apply Continuous.mul continuous_const
    apply Continuous.add
    · apply Continuous.mul
      · exact (Complex.continuous_ofReal.comp (continuous_apply 0)).add continuous_const
      · exact continuous_const
    · apply Continuous.mul
      · exact (Complex.continuous_ofReal.comp (continuous_apply 1)).add continuous_const
      · exact continuous_const

lemma continuous_slice_map (y : Fin 2 → ℝ) :
    Continuous (fun (x : Fin 2 → ℝ) => (fun i : Fin 2 => (x i : ℂ) + I * (y i : ℂ))) := by
  apply continuous_pi
  intro i
  exact (Complex.continuous_ofReal.comp (continuous_apply i)).add continuous_const

lemma bochner_f_cont_of_holo (r R : ℝ) (f : (Fin 2 → ℂ) → ℂ)
    (hf_holo : DifferentiableOn ℂ f (TubeDomain (LShape r R)))
    (y : Fin 2 → ℝ) (hy : y ∈ LShape r R) :
    Continuous (fun x : Fin 2 → ℝ => f (fun i => ↑(x i) + I * ↑(y i))) := by
  have h_maps : ∀ x : Fin 2 → ℝ,
      (fun i : Fin 2 => (x i : ℂ) + I * (y i : ℂ)) ∈ TubeDomain (LShape r R) := by
    intro x
    simp only [TubeDomain, mem_setOf_eq]
    have h_im : (fun i => ((x i : ℂ) + I * (y i : ℂ)).im) = y := by
      ext i
      simp
    rw [h_im]
    exact hy
  exact ContinuousOn.comp_continuous hf_holo.continuousOn (continuous_slice_map y) h_maps

lemma bochner_integrand_aestronglyMeasurable_2d (r R : ℝ) (f : (Fin 2 → ℂ) → ℂ)
    (hf_holo : DifferentiableOn ℂ f (TubeDomain (LShape r R)))
    (ε : ℝ) (ξ : Fin 2 → ℝ) (y : Fin 2 → ℝ) (hy : y ∈ LShape r R) :
    AEStronglyMeasurable
      (fun x : Fin 2 → ℝ => bochner_integrand_F f ε ξ (fun i => ↑(x i) + I * ↑(y i))) volume := by
  have h_cont := bochner_integrand_continuous_2d f ε ξ y (bochner_f_cont_of_holo r R f hf_holo y hy)
  exact h_cont.aestronglyMeasurable

lemma bochner_integrand_integrable_2d (r R : ℝ) (f : (Fin 2 → ℂ) → ℂ)
    (hf_holo : DifferentiableOn ℂ f (TubeDomain (LShape r R)))
    (hf_bound : ∃ M : ℝ, ∀ z : Fin 2 → ℂ, ‖f z‖ ≤ M)
    (ε : ℝ) (hε : 0 < ε) (ξ : Fin 2 → ℝ) (y : Fin 2 → ℝ) (hy : y ∈ LShape r R) :
    Integrable (fun x : Fin 2 → ℝ => bochner_integrand_F f ε ξ (fun i => ↑(x i) + I * ↑(y i))) := by
  rcases bochner_integrand_bound_2d f hf_bound ε ξ y with ⟨C, h_bound⟩
  have h_meas := bochner_integrand_aestronglyMeasurable_2d r R f hf_holo ε ξ y hy
  exact bochner_integrand_integrable_of_bound f ε hε ξ y C h_bound h_meas

lemma bochner_integrand_integral_norm_le (r R : ℝ) (f : (Fin 2 → ℂ) → ℂ)
    (hf_holo : DifferentiableOn ℂ f (TubeDomain (LShape r R)))
    (M : ℝ) (hM : ∀ z : Fin 2 → ℂ, ‖f z‖ ≤ M)
    (ε : ℝ) (hε : 0 < ε) (ξ : Fin 2 → ℝ) (y : Fin 2 → ℝ) (hy : y ∈ LShape r R) :
    (∫ (x : Fin 2 → ℝ), ‖bochner_integrand_F f ε ξ (fun i => ↑(x i) + I * ↑(y i))‖) ≤
      (max M 0 * Real.exp (ε * (y 0 ^ 2 + y 1 ^ 2)) *
        ∫ (x : Fin 2 → ℝ), Real.exp (-ε * (x 0 ^ 2 + x 1 ^ 2))) *
        Real.exp (y 0 * ξ 0 + y 1 * ξ 1) := by
  let C0 := max M 0 * Real.exp (ε * (y 0 ^ 2 + y 1 ^ 2))
  have hint_gauss : Integrable (fun x : Fin 2 → ℝ => Real.exp (-ε * (x 0 ^ 2 + x 1 ^ 2))) :=
    integrable_gaussian_2d ε hε
  have h_int_bound : Integrable (fun x : Fin 2 → ℝ =>
      (C0 * Real.exp (y 0 * ξ 0 + y 1 * ξ 1)) * Real.exp (-ε * (x 0 ^ 2 + x 1 ^ 2))) :=
    hint_gauss.const_mul _
  have h_meas := (bochner_integrand_aestronglyMeasurable_2d r R f hf_holo ε ξ y hy).norm
  have h_le := integral_mono_of_nonneg (ae_of_all _ (fun _ => norm_nonneg _)) h_int_bound
    (ae_of_all _ (bochner_integrand_norm_le_gaussian f M hM ε ξ y))
  have h_eq : (∫ (x : Fin 2 → ℝ),
        (C0 * Real.exp (y 0 * ξ 0 + y 1 * ξ 1)) * Real.exp (-ε * (x 0 ^ 2 + x 1 ^ 2))) =
      (C0 * ∫ (x : Fin 2 → ℝ), Real.exp (-ε * (x 0 ^ 2 + x 1 ^ 2))) *
        Real.exp (y 0 * ξ 0 + y 1 * ξ 1) := by
    rw [MeasureTheory.integral_const_mul]
    ring
  rw [h_eq] at h_le
  exact h_le

lemma bochner_shift_axis1 (r R : ℝ) (_hr : 0 < r) (_hR : r < R)
    (f : (Fin 2 → ℂ) → ℂ) (hf_holo : DifferentiableOn ℂ f (TubeDomain (LShape r R)))
    (hf_bound : ∃ M : ℝ, ∀ z : Fin 2 → ℂ, ‖f z‖ ≤ M)
    (ε : ℝ) (hε : 0 < ε) (ξ : Fin 2 → ℝ)
    (y₀ y₁ y₁' : ℝ)
    (h_path : ∀ t ∈ uIcc y₁ y₁', ![y₀, t] ∈ LShape r R) :
    ∫ (x : Fin 2 → ℝ), bochner_integrand_F f ε ξ ![↑(x 0) + I * ↑y₀, ↑(x 1) + I * ↑y₁] =
    ∫ (x : Fin 2 → ℝ), bochner_integrand_F f ε ξ ![↑(x 0) + I * ↑y₀, ↑(x 1) + I * ↑y₁'] := by
  have hy1_eq : (fun x : Fin 2 → ℝ =>
      bochner_integrand_F f ε ξ ![↑(x 0) + I * ↑y₀, ↑(x 1) + I * ↑y₁]) =
      (fun x : Fin 2 → ℝ => bochner_integrand_F f ε ξ (fun i => ↑(x i) + I * ↑(![y₀, y₁] i))) := by
    ext x
    congr 1
    ext i
    fin_cases i <;> rfl
  have hy1'_eq : (fun x : Fin 2 → ℝ =>
      bochner_integrand_F f ε ξ ![↑(x 0) + I * ↑y₀, ↑(x 1) + I * ↑y₁']) =
      (fun x : Fin 2 → ℝ => bochner_integrand_F f ε ξ (fun i => ↑(x i) + I * ↑(![y₀, y₁'] i))) := by
    ext x
    congr 1
    ext i
    fin_cases i <;> rfl
  have hint1 : Integrable
      (fun x : Fin 2 → ℝ => bochner_integrand_F f ε ξ ![↑(x 0) + I * ↑y₀, ↑(x 1) + I * ↑y₁]) := by
    rw [hy1_eq]
    exact bochner_integrand_integrable_2d r R f hf_holo hf_bound ε hε ξ ![y₀, y₁]
      (h_path y₁ left_mem_uIcc)
  have hint2 : Integrable
      (fun x : Fin 2 → ℝ => bochner_integrand_F f ε ξ ![↑(x 0) + I * ↑y₀, ↑(x 1) + I * ↑y₁']) := by
    rw [hy1'_eq]
    exact bochner_integrand_integrable_2d r R f hf_holo hf_bound ε hε ξ ![y₀, y₁']
      (h_path y₁' right_mem_uIcc)
  rw [integral_finTwo_eq_integral_prod _ hint1]
  rw [integral_finTwo_eq_integral_prod _ hint2]
  congr 1
  ext x₀
  let g : ℂ → ℂ := fun w => bochner_integrand_F f ε ξ ![↑x₀ + I * ↑y₀, w]
  have hg_holo : DifferentiableOn ℂ g {w : ℂ | w.im ∈ uIcc y₁ y₁'} :=
    bochner_slice1_diffOn r R f hf_holo ε ξ x₀ y₀ y₁ y₁' h_path
  have hg_bound : ∃ C : ℝ, ∀ w : ℂ, w.im ∈ uIcc y₁ y₁' → ‖g w‖ ≤ C * Real.exp (-ε * w.re ^ 2) :=
    bochner_slice1_bound r R f hf_bound ε hε ξ x₀ y₀ y₁ y₁'
  have h_shift := fourier_shift_1d_eps_uIcc y₁ y₁' ε hε g hg_holo hg_bound
  exact h_shift

lemma diff_affine_slice0 (z₁ : ℂ) :
    Differentiable ℂ (fun w : ℂ => (![w, z₁] : Fin 2 → ℂ)) := by
  apply differentiable_pi.mpr
  intro i
  fin_cases i
  · exact differentiable_id
  · exact differentiable_const z₁

lemma bochner_slice0_diffOn (r R : ℝ)
    (f : (Fin 2 → ℂ) → ℂ) (hf_holo : DifferentiableOn ℂ f (TubeDomain (LShape r R)))
    (ε : ℝ) (ξ : Fin 2 → ℝ) (x₁ y₀ y₀' y₁ : ℝ)
    (h_path : ∀ s ∈ uIcc y₀ y₀', ![s, y₁] ∈ LShape r R) :
    DifferentiableOn ℂ (fun w => bochner_integrand_F f ε ξ ![w, ↑x₁ + I * ↑y₁])
      {w : ℂ | w.im ∈ uIcc y₀ y₀'} := by
  let z₁ : ℂ := ↑x₁ + I * ↑y₁
  have hz₁_im : z₁.im = y₁ := by simp [z₁]
  let L : ℂ → (Fin 2 → ℂ) := fun w => ![w, z₁]
  have hL_diff : Differentiable ℂ L := diff_affine_slice0 z₁
  have h_maps : MapsTo L {w : ℂ | w.im ∈ uIcc y₀ y₀'} (TubeDomain (LShape r R)) := by
    intro w hw
    simp only [mem_setOf_eq] at hw
    simp only [TubeDomain, mem_setOf_eq]
    have h_im : (fun i => (L w i).im) = ![w.im, y₁] := by
      ext i
      fin_cases i
      · simp [L]
      · simp [L, hz₁_im]
    rw [h_im]
    exact h_path w.im hw
  have hf_comp : DifferentiableOn ℂ (f ∘ L) {w : ℂ | w.im ∈ uIcc y₀ y₀'} :=
    hf_holo.comp hL_diff.differentiableOn h_maps
  have h_f_eps : DifferentiableOn ℂ (fun w => bochner_f_eps f ε (L w))
      {w : ℂ | w.im ∈ uIcc y₀ y₀'} := by
    unfold bochner_f_eps
    apply DifferentiableOn.mul hf_comp
    have h_exp : Differentiable ℂ (fun w => Complex.exp (-↑ε * ((L w 0) ^ 2 + (L w 1) ^ 2))) := by
      apply Differentiable.comp Complex.differentiable_exp
      apply Differentiable.mul (differentiable_const _)
      apply Differentiable.add
      · exact (differentiable_pi.mp hL_diff 0).pow 2
      · exact (differentiable_pi.mp hL_diff 1).pow 2
    exact h_exp.differentiableOn
  unfold bochner_integrand_F
  apply DifferentiableOn.mul h_f_eps
  have h_fourier : Differentiable ℂ
      (fun w => Complex.exp (-I * (L w 0 * ↑(ξ 0) + L w 1 * ↑(ξ 1)))) := by
    apply Differentiable.comp Complex.differentiable_exp
    apply Differentiable.mul (differentiable_const _)
    apply Differentiable.add
    · exact (differentiable_pi.mp hL_diff 0).mul (differentiable_const _)
    · exact (differentiable_pi.mp hL_diff 1).mul (differentiable_const _)
  exact h_fourier.differentiableOn

lemma bochner_slice0_bound_const (f : (Fin 2 → ℂ) → ℂ)
    (hf_bound : ∃ M : ℝ, ∀ z : Fin 2 → ℂ, ‖f z‖ ≤ M)
    (ε : ℝ) (hε : 0 ≤ ε) (ξ : Fin 2 → ℝ) (x₁ y₀ y₀' y₁ : ℝ) :
    ∃ C : ℝ, ∀ w : ℂ, w.im ∈ uIcc y₀ y₀' →
      ‖bochner_integrand_F f ε ξ ![w, ↑x₁ + I * ↑y₁]‖ ≤ C * Real.exp (-ε * w.re ^ 2) := by
  rcases hf_bound with ⟨M, hM⟩
  let K := max (|y₀|) (|y₀'|)
  let C := max M 0 * Real.exp (-ε * x₁ ^ 2) * Real.exp (ε * (K ^ 2 + y₁ ^ 2)) *
    Real.exp (K * |ξ 0| + y₁ * ξ 1)
  use C
  intro w hw
  have h_rep : ![w, ↑x₁ + I * ↑y₁] = fun i => ↑(![w.re, x₁] i) + I * ↑(![w.im, y₁] i) := by
    ext i
    fin_cases i
    · simp [mul_comm I ↑w.im, Complex.re_add_im]
    · simp
  rw [h_rep]
  rw [bochner_integrand_norm_eq]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have h_bound_f : ‖f (fun i => ↑(![w.re, x₁] i) + I * ↑(![w.im, y₁] i))‖ ≤ max M 0 :=
    le_trans (hM _) (le_max_left M 0)
  have h_gauss : Real.exp (-ε * (w.re ^ 2 + x₁ ^ 2)) =
      Real.exp (-ε * w.re ^ 2) * Real.exp (-ε * x₁ ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [h_gauss]
  have h_sq_le : w.im ^ 2 ≤ K ^ 2 := sq_le_sq_of_bound y₀ y₀' w.im hw
  have h_exp_y : Real.exp (ε * (w.im ^ 2 + y₁ ^ 2)) ≤ Real.exp (ε * (K ^ 2 + y₁ ^ 2)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have h_mul_le : w.im * ξ 0 ≤ K * |ξ 0| := mul_le_mul_of_bound y₀ y₀' (ξ 0) w.im hw
  have h_exp_xi : Real.exp (w.im * ξ 0 + y₁ * ξ 1) ≤ Real.exp (K * |ξ 0| + y₁ * ξ 1) := by
    apply Real.exp_le_exp.mpr
    linarith
  have h_rew1 : ‖f (fun i => ↑(![w.re, x₁] i) + I * ↑(![w.im, y₁] i))‖ *
      (Real.exp (-ε * w.re ^ 2) * Real.exp (-ε * x₁ ^ 2)) *
      Real.exp (ε * (w.im ^ 2 + y₁ ^ 2)) * Real.exp (w.im * ξ 0 + y₁ * ξ 1) =
      (‖f (fun i => ↑(![w.re, x₁] i) + I * ↑(![w.im, y₁] i))‖ *
      Real.exp (-ε * x₁ ^ 2) *
      Real.exp (ε * (w.im ^ 2 + y₁ ^ 2)) * Real.exp (w.im * ξ 0 + y₁ * ξ 1)) *
      Real.exp (-ε * w.re ^ 2) := by ring
  rw [h_rew1]
  dsimp [C]
  have h_le_core : ‖f (fun i => ↑(![w.re, x₁] i) + I * ↑(![w.im, y₁] i))‖ *
      Real.exp (-ε * x₁ ^ 2) *
      Real.exp (ε * (w.im ^ 2 + y₁ ^ 2)) * Real.exp (w.im * ξ 0 + y₁ * ξ 1) ≤
      max M 0 * Real.exp (-ε * x₁ ^ 2) * Real.exp (ε * (K ^ 2 + y₁ ^ 2)) *
        Real.exp (K * |ξ 0| + y₁ * ξ 1) := by
    have h1 : 0 ≤ Real.exp (-ε * x₁ ^ 2) := (Real.exp_pos _).le
    have h2 : 0 ≤ Real.exp (ε * (w.im ^ 2 + y₁ ^ 2)) := (Real.exp_pos _).le
    have h3 : 0 ≤ Real.exp (w.im * ξ 0 + y₁ * ξ 1) := (Real.exp_pos _).le
    gcongr
  exact mul_le_mul_of_nonneg_right h_le_core (Real.exp_pos _).le

lemma bochner_slice0_bound (_r _R : ℝ)
    (f : (Fin 2 → ℂ) → ℂ)
    (hf_bound : ∃ M : ℝ, ∀ z : Fin 2 → ℂ, ‖f z‖ ≤ M)
    (ε : ℝ) (hε : 0 < ε) (ξ : Fin 2 → ℝ) (x₁ y₀ y₀' y₁ : ℝ) :
    ∃ C : ℝ, ∀ w : ℂ, w.im ∈ uIcc y₀ y₀' →
      ‖bochner_integrand_F f ε ξ ![w, ↑x₁ + I * ↑y₁]‖ ≤ C * Real.exp (-ε * w.re ^ 2) := by
  exact bochner_slice0_bound_const f hf_bound ε hε.le ξ x₁ y₀ y₀' y₁

lemma integral_finTwo_eq_integral_prod_swap (g : (Fin 2 → ℝ) → ℂ) (hg : Integrable g) :
    ∫ (x : Fin 2 → ℝ), g x = ∫ (x₁ : ℝ), ∫ (x₀ : ℝ), g ![x₀, x₁] := by
  rw [integral_finTwo_eq_integral_prod g hg]
  have h_pres := volume_preserving_finTwoArrow ℝ
  have h_emb := (@MeasurableEquiv.finTwoArrow ℝ _).measurableEmbedding
  have h_int_iff := h_pres.integrable_comp_emb h_emb (g := fun p : ℝ × ℝ => g ![p.1, p.2])
  have h_comp : (fun p : ℝ × ℝ => g ![p.1, p.2]) ∘ (⇑MeasurableEquiv.finTwoArrow) = g := by
    ext x
    simp only [Function.comp_apply, MeasurableEquiv.finTwoArrow_apply]
    congr 1
    ext i
    fin_cases i <;> rfl
  rw [h_comp] at h_int_iff
  have h_int_prod : Integrable (fun p : ℝ × ℝ => g ![p.1, p.2]) volume := h_int_iff.mp hg
  exact integral_integral_swap (f := fun x₀ x₁ => g ![x₀, x₁]) h_int_prod

lemma bochner_shift_axis0 (r R : ℝ) (_hr : 0 < r) (_hR : r < R)
    (f : (Fin 2 → ℂ) → ℂ) (hf_holo : DifferentiableOn ℂ f (TubeDomain (LShape r R)))
    (hf_bound : ∃ M : ℝ, ∀ z : Fin 2 → ℂ, ‖f z‖ ≤ M)
    (ε : ℝ) (hε : 0 < ε) (ξ : Fin 2 → ℝ)
    (y₀ y₀' y₁ : ℝ)
    (h_path : ∀ s ∈ uIcc y₀ y₀', ![s, y₁] ∈ LShape r R) :
    ∫ (x : Fin 2 → ℝ), bochner_integrand_F f ε ξ ![↑(x 0) + I * ↑y₀, ↑(x 1) + I * ↑y₁] =
    ∫ (x : Fin 2 → ℝ), bochner_integrand_F f ε ξ ![↑(x 0) + I * ↑y₀', ↑(x 1) + I * ↑y₁] := by
  have hy0_eq : (fun x : Fin 2 → ℝ =>
      bochner_integrand_F f ε ξ ![↑(x 0) + I * ↑y₀, ↑(x 1) + I * ↑y₁]) =
      (fun x : Fin 2 → ℝ => bochner_integrand_F f ε ξ (fun i => ↑(x i) + I * ↑(![y₀, y₁] i))) := by
    ext x
    congr 1
    ext i
    fin_cases i <;> rfl
  have hy0'_eq : (fun x : Fin 2 → ℝ =>
      bochner_integrand_F f ε ξ ![↑(x 0) + I * ↑y₀', ↑(x 1) + I * ↑y₁]) =
      (fun x : Fin 2 → ℝ => bochner_integrand_F f ε ξ (fun i => ↑(x i) + I * ↑(![y₀', y₁] i))) := by
    ext x
    congr 1
    ext i
    fin_cases i <;> rfl
  have hint1 : Integrable
      (fun x : Fin 2 → ℝ => bochner_integrand_F f ε ξ ![↑(x 0) + I * ↑y₀, ↑(x 1) + I * ↑y₁]) := by
    rw [hy0_eq]
    exact bochner_integrand_integrable_2d r R f hf_holo hf_bound ε hε ξ ![y₀, y₁]
      (h_path y₀ left_mem_uIcc)
  have hint2 : Integrable
      (fun x : Fin 2 → ℝ => bochner_integrand_F f ε ξ ![↑(x 0) + I * ↑y₀', ↑(x 1) + I * ↑y₁]) := by
    rw [hy0'_eq]
    exact bochner_integrand_integrable_2d r R f hf_holo hf_bound ε hε ξ ![y₀', y₁]
      (h_path y₀' right_mem_uIcc)
  rw [integral_finTwo_eq_integral_prod_swap _ hint1]
  rw [integral_finTwo_eq_integral_prod_swap _ hint2]
  congr 1
  ext x₁
  let g : ℂ → ℂ := fun w => bochner_integrand_F f ε ξ ![w, ↑x₁ + I * ↑y₁]
  have hg_holo : DifferentiableOn ℂ g {w : ℂ | w.im ∈ uIcc y₀ y₀'} :=
    bochner_slice0_diffOn r R f hf_holo ε ξ x₁ y₀ y₀' y₁ h_path
  have hg_bound : ∃ C : ℝ, ∀ w : ℂ, w.im ∈ uIcc y₀ y₀' → ‖g w‖ ≤ C * Real.exp (-ε * w.re ^ 2) :=
    bochner_slice0_bound r R f hf_bound ε hε ξ x₁ y₀ y₀' y₁
  have h_shift := fourier_shift_1d_eps_uIcc y₀ y₀' ε hε g hg_holo hg_bound
  exact h_shift

lemma mem_uIcc_of_mem_Ioo {a b x y : ℝ} (hx : x ∈ Ioo a b) (hy : y ∈ Ioo a b)
    {t : ℝ} (ht : t ∈ uIcc x y) : t ∈ Ioo a b := by
  rw [uIcc] at ht
  constructor
  · calc a < min x y := lt_min hx.1 hy.1
    _ ≤ t := ht.1
  · calc t ≤ max x y := ht.2
    _ < b := max_lt hx.2 hy.2

lemma bochner_shift_to_center (r R : ℝ) (hr : 0 < r) (hR : r < R)
    (f : (Fin 2 → ℂ) → ℂ) (hf_holo : DifferentiableOn ℂ f (TubeDomain (LShape r R)))
    (hf_bound : ∃ M : ℝ, ∀ z : Fin 2 → ℂ, ‖f z‖ ≤ M)
    (ε : ℝ) (hε : 0 < ε) (ξ : Fin 2 → ℝ)
    (y : Fin 2 → ℝ) (hy : y ∈ LShape r R) :
    ∫ (x : Fin 2 → ℝ), bochner_integrand_F f ε ξ (fun i => ↑(x i) + I * ↑(y i)) =
    ∫ (x : Fin 2 → ℝ), bochner_integrand_F f ε ξ (fun i => ↑(x i) + I * (r / 2)) := by
  have hr2_pos : 0 < r / 2 := by linarith
  have hr2_lt_r : r / 2 < r := by linarith
  have hr2_lt_R : r / 2 < R := by linarith
  have hr2_mem_r : r / 2 ∈ Ioo 0 r := ⟨hr2_pos, hr2_lt_r⟩
  have hr2_mem_R : r / 2 ∈ Ioo 0 R := ⟨hr2_pos, hr2_lt_R⟩
  have hy_eq : (fun (x : Fin 2 → ℝ) => bochner_integrand_F f ε ξ (fun i => ↑(x i) + I * ↑(y i))) =
      (fun (x : Fin 2 → ℝ) =>
        bochner_integrand_F f ε ξ ![↑(x 0) + I * ↑(y 0), ↑(x 1) + I * ↑(y 1)]) := by
    ext x
    congr 1
    ext i
    fin_cases i <;> rfl
  have hcenter_eq :
      (fun (x : Fin 2 → ℝ) => bochner_integrand_F f ε ξ (fun i => ↑(x i) + I * (r / 2))) =
      (fun (x : Fin 2 → ℝ) =>
        bochner_integrand_F f ε ξ ![↑(x 0) + I * ↑(r / 2), ↑(x 1) + I * ↑(r / 2)]) := by
    ext x
    congr 1
    ext i
    fin_cases i <;> (dsimp; push_cast; rfl)
  rw [hy_eq, hcenter_eq]
  rcases hy with ⟨hy0_pos, hy0_r, hy1_pos, hy1_R⟩ | ⟨hy0_pos, hy0_R, hy1_pos, hy1_r⟩
  · have hpath1 : ∀ t ∈ uIcc (y 1) (r / 2), ![y 0, t] ∈ LShape r R := by
      intro t ht
      have ht_mem := mem_uIcc_of_mem_Ioo ⟨hy1_pos, hy1_R⟩ hr2_mem_R ht
      unfold LShape
      left
      exact ⟨hy0_pos, hy0_r, ht_mem.1, ht_mem.2⟩
    have h1 := bochner_shift_axis1 r R hr hR f hf_holo hf_bound ε hε ξ (y 0) (y 1) (r / 2) hpath1
    have hpath0 : ∀ s ∈ uIcc (y 0) (r / 2), ![s, r / 2] ∈ LShape r R := by
      intro s hs
      have hs_mem := mem_uIcc_of_mem_Ioo ⟨hy0_pos, hy0_r⟩ hr2_mem_r hs
      unfold LShape
      left
      exact ⟨hs_mem.1, hs_mem.2, hr2_pos, hr2_lt_R⟩
    have h0 := bochner_shift_axis0 r R hr hR f hf_holo hf_bound ε hε ξ (y 0) (r / 2) (r / 2) hpath0
    rw [h1, h0]
  · have hpath0 : ∀ s ∈ uIcc (y 0) (r / 2), ![s, y 1] ∈ LShape r R := by
      intro s hs
      have hs_mem := mem_uIcc_of_mem_Ioo ⟨hy0_pos, hy0_R⟩ hr2_mem_R hs
      unfold LShape
      right
      exact ⟨hs_mem.1, hs_mem.2, hy1_pos, hy1_r⟩
    have h0 := bochner_shift_axis0 r R hr hR f hf_holo hf_bound ε hε ξ (y 0) (r / 2) (y 1) hpath0
    have hpath1 : ∀ t ∈ uIcc (y 1) (r / 2), ![r / 2, t] ∈ LShape r R := by
      intro t ht
      have ht_mem := mem_uIcc_of_mem_Ioo ⟨hy1_pos, hy1_r⟩ hr2_mem_r ht
      unfold LShape
      right
      exact ⟨hr2_pos, hr2_lt_R, ht_mem.1, ht_mem.2⟩
    have h1 := bochner_shift_axis1 r R hr hR f hf_holo hf_bound ε hε ξ (r / 2) (y 1) (r / 2) hpath1
    rw [h0, h1]

lemma bochner_fourier_transform_shift_eps (r R : ℝ) (hr : 0 < r) (hR : r < R)
    (f : (Fin 2 → ℂ) → ℂ) (hf_holo : DifferentiableOn ℂ f (TubeDomain (LShape r R)))
    (hf_bound : ∃ M : ℝ, ∀ z : Fin 2 → ℂ, ‖f z‖ ≤ M)
    (ε : ℝ) (hε : 0 < ε)
    (y₁ y₂ : Fin 2 → ℝ) (hy₁ : (fun i => ↑(0 : ℝ) + I * ↑(y₁ i)) ∈ TubeDomain (LShape r R))
    (hy₂ : (fun i => ↑(0 : ℝ) + I * ↑(y₂ i)) ∈ TubeDomain (LShape r R)) (ξ : Fin 2 → ℝ) :
    bochner_fourier_transform_eps f ε y₁ ξ * Real.exp (y₁ 0 * ξ 0 + y₁ 1 * ξ 1) =
    bochner_fourier_transform_eps f ε y₂ ξ * Real.exp (y₂ 0 * ξ 0 + y₂ 1 * ξ 1) := by
  have hy₁_LS : y₁ ∈ LShape r R := (mem_TubeDomain_pure_imag (LShape r R) y₁).mp hy₁
  have hy₂_LS : y₂ ∈ LShape r R := (mem_TubeDomain_pure_imag (LShape r R) y₂).mp hy₂
  have H1 := bochner_fourier_mul_exp_eq_integral f ε y₁ ξ
  have H2 := bochner_fourier_mul_exp_eq_integral f ε y₂ ξ
  have h_center1 := bochner_shift_to_center r R hr hR f hf_holo hf_bound ε hε ξ y₁ hy₁_LS
  have h_center2 := bochner_shift_to_center r R hr hR f hf_holo hf_bound ε hε ξ y₂ hy₂_LS
  have h_eq : (bochner_fourier_transform_eps f ε y₁ ξ * ↑(Real.exp (y₁ 0 * ξ 0 + y₁ 1 * ξ 1))) =
      (bochner_fourier_transform_eps f ε y₂ ξ * ↑(Real.exp (y₂ 0 * ξ 0 + y₂ 1 * ξ 1))) := by
    rw [H1, H2, h_center1, h_center2]
  exact h_eq

lemma bochner_c_eps_norm_le (r R : ℝ) (hr : 0 < r) (hR : r < R)
    (f : (Fin 2 → ℂ) → ℂ) (hf_holo : DifferentiableOn ℂ f (TubeDomain (LShape r R)))
    (hf_bound : ∃ M : ℝ, ∀ z : Fin 2 → ℂ, ‖f z‖ ≤ M)
    (ε : ℝ) (hε : 0 < ε)
    (y : Fin 2 → ℝ)
    (hy : (fun i => ↑(0 : ℝ) + Complex.I * ↑(y i)) ∈ TubeDomain (LShape r R)) (ξ : Fin 2 → ℝ) :
    ‖bochner_fourier_transform_eps f ε (fun _ => r/2) ξ * ↑(Real.exp ((r/2) * ξ 0 + (r/2) * ξ 1))‖ =
      ‖bochner_fourier_transform_eps f ε y ξ * ↑(Real.exp (y 0 * ξ 0 + y 1 * ξ 1))‖ := by
  have hy0 : (fun _ : Fin 2 => r / 2) ∈ LShape r R := by
    unfold LShape
    left
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hy0_tube :
      (fun i => ↑(0 : ℝ) + Complex.I * ↑((fun _ : Fin 2 => r / 2) i)) ∈
        TubeDomain (LShape r R) := by
    simp [TubeDomain, hy0]
  have h_shift := bochner_fourier_transform_shift_eps r R hr hR f hf_holo hf_bound ε hε
    (fun _ => r/2) y hy0_tube hy ξ
  rw [h_shift]

lemma bochner_fourier_mul_exp_norm_le_integral_norm
    (f : (Fin 2 → ℂ) → ℂ) (ε : ℝ) (y ξ : Fin 2 → ℝ) :
    ‖bochner_fourier_transform_eps f ε y ξ * ↑(Real.exp (y 0 * ξ 0 + y 1 * ξ 1))‖ ≤
      ∫ (x : Fin 2 → ℝ), ‖bochner_integrand_F f ε ξ (fun i => ↑(x i) + I * ↑(y i))‖ := by
  have h_int_eq := bochner_fourier_mul_exp_eq_integral f ε y ξ
  have h_norm_eq : ‖bochner_fourier_transform_eps f ε y ξ * ↑(Real.exp (y 0 * ξ 0 + y 1 * ξ 1))‖ =
      ‖∫ (x : Fin 2 → ℝ), bochner_integrand_F f ε ξ (fun i => ↑(x i) + I * ↑(y i))‖ :=
    congr_arg norm h_int_eq
  exact h_norm_eq.le.trans (norm_integral_le_integral_norm _)

lemma bochner_fourier_mul_exp_norm_le_gaussian (r R : ℝ)
    (f : (Fin 2 → ℂ) → ℂ) (hf_holo : DifferentiableOn ℂ f (TubeDomain (LShape r R)))
    (M : ℝ) (hM : ∀ z : Fin 2 → ℂ, ‖f z‖ ≤ M)
    (ε : ℝ) (hε : 0 < ε)
    (y : Fin 2 → ℝ) (hy : y ∈ LShape r R) (ξ : Fin 2 → ℝ) :
    ‖bochner_fourier_transform_eps f ε y ξ * ↑(Real.exp (y 0 * ξ 0 + y 1 * ξ 1))‖ ≤
      (max M 0 * Real.exp (ε * (y 0 ^ 2 + y 1 ^ 2)) *
        ∫ (x : Fin 2 → ℝ), Real.exp (-ε * (x 0 ^ 2 + x 1 ^ 2))) *
        Real.exp (y 0 * ξ 0 + y 1 * ξ 1) := by
  have h1 := bochner_fourier_mul_exp_norm_le_integral_norm f ε y ξ
  have h2 := bochner_integrand_integral_norm_le r R f hf_holo M hM ε hε ξ y hy
  exact h1.trans h2

lemma bochner_c_eps_pointwise_bound (r R : ℝ) (hr : 0 < r) (hR : r < R)
    (f : (Fin 2 → ℂ) → ℂ) (hf_holo : DifferentiableOn ℂ f (TubeDomain (LShape r R)))
    (M : ℝ) (hM : ∀ z : Fin 2 → ℂ, ‖f z‖ ≤ M)
    (ε : ℝ) (hε : 0 < ε)
    (y : Fin 2 → ℝ) (hy : y ∈ LShape r R) (ξ : Fin 2 → ℝ) :
    ‖bochner_fourier_transform_eps f ε (fun _ => r/2) ξ * ↑(Real.exp ((r/2) * ξ 0 + (r/2) * ξ 1))‖ ≤
      (max M 0 * Real.exp (ε * (y 0 ^ 2 + y 1 ^ 2)) *
        ∫ (x : Fin 2 → ℝ), Real.exp (-ε * (x 0 ^ 2 + x 1 ^ 2))) *
        Real.exp (y 0 * ξ 0 + y 1 * ξ 1) := by
  have hy_tube : (fun i => ↑(0 : ℝ) + Complex.I * ↑(y i)) ∈ TubeDomain (LShape r R) :=
    (mem_TubeDomain_pure_imag (LShape r R) y).mpr hy
  have h_shift := bochner_c_eps_norm_le r R hr hR f hf_holo ⟨M, hM⟩ ε hε y hy_tube ξ
  exact h_shift.le.trans (bochner_fourier_mul_exp_norm_le_gaussian r R f hf_holo M hM ε hε y hy ξ)

lemma bochner_c_eps_bound_of_y (r R : ℝ) (hr : 0 < r) (hR : r < R)
    (f : (Fin 2 → ℂ) → ℂ) (hf_holo : DifferentiableOn ℂ f (TubeDomain (LShape r R)))
    (hf_bound : ∃ M : ℝ, ∀ z : Fin 2 → ℂ, ‖f z‖ ≤ M)
    (ε : ℝ) (hε : 0 < ε)
    (y : Fin 2 → ℝ) (hy : y ∈ LShape r R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : Fin 2 → ℝ,
      ‖bochner_fourier_transform_eps f ε (fun _ => r/2) ξ *
        ↑(Real.exp ((r/2) * ξ 0 + (r/2) * ξ 1))‖ ≤
        C * Real.exp (y 0 * ξ 0 + y 1 * ξ 1) := by
  rcases hf_bound with ⟨M, hM⟩
  let C := max M 0 * Real.exp (ε * (y 0 ^ 2 + y 1 ^ 2)) *
    ∫ (x : Fin 2 → ℝ), Real.exp (-ε * (x 0 ^ 2 + x 1 ^ 2))
  have hC : 0 ≤ C := by
    have hI : 0 ≤ ∫ (x : Fin 2 → ℝ), Real.exp (-ε * (x 0 ^ 2 + x 1 ^ 2)) :=
      integral_nonneg (fun _ => (Real.exp_pos _).le)
    dsimp [C]
    positivity
  refine ⟨C, hC, fun ξ => bochner_c_eps_pointwise_bound r R hr hR f hf_holo M hM ε hε y hy ξ⟩

lemma box_eq_pi (R : ℝ) :
    {x : Fin 2 → ℝ | ∀ i, 0 < x i ∧ x i < R} = Set.pi Set.univ (fun _ : Fin 2 => Set.Ioo 0 R) := by
  ext x
  simp [Set.mem_pi, Set.mem_Ioo]

lemma convex_box (R : ℝ) :
    Convex ℝ {x : Fin 2 → ℝ | ∀ i, 0 < x i ∧ x i < R} := by
  rw [box_eq_pi]
  exact convex_pi (fun _ _ => convex_Ioo 0 R)

lemma LShape_subset_box {r R : ℝ} (hR : r < R) :
    LShape r R ⊆ {x : Fin 2 → ℝ | ∀ i, 0 < x i ∧ x i < R} := by
  intro x hx i
  fin_cases i
  · rcases hx with ⟨h0, h0r, h1, h1R⟩ | ⟨h0, h0R, h1, h1r⟩
    · exact ⟨h0, h0r.trans hR⟩
    · exact ⟨h0, h0R⟩
  · rcases hx with ⟨h0, h0r, h1, h1R⟩ | ⟨h0, h0R, h1, h1r⟩
    · exact ⟨h1, h1R⟩
    · exact ⟨h1, h1r.trans hR⟩

lemma LShapeConvexHull_subset_box {r R : ℝ} (hR : r < R) :
    LShapeConvexHull r R ⊆ {x : Fin 2 → ℝ | ∀ i, 0 < x i ∧ x i < R} :=
  convexHull_min (LShape_subset_box hR) (convex_box R)

lemma mem_LShapeConvexHull_bounds {r R : ℝ} (hR : r < R)
    {y : Fin 2 → ℝ} (hy : y ∈ LShapeConvexHull r R) :
    0 < y 0 ∧ y 0 < R ∧ 0 < y 1 ∧ y 1 < R := by
  have h := LShapeConvexHull_subset_box hR hy
  exact ⟨(h 0).1, (h 0).2, (h 1).1, (h 1).2⟩

lemma LShape_subset_sum_lt {r R : ℝ} :
    LShape r R ⊆ {x : Fin 2 → ℝ | x 0 + x 1 < r + R} := by
  intro x hx
  dsimp
  rcases hx with ⟨h0, h0r, h1, h1R⟩ | ⟨h0, h0R, h1, h1r⟩
  · linarith
  · linarith

lemma convex_halfspace_sum (c : ℝ) :
    Convex ℝ {x : Fin 2 → ℝ | x 0 + x 1 < c} := by
  intro x hx y hy a b ha hb hab
  dsimp at hx hy ⊢
  rcases ha.eq_or_lt with rfl | ha_pos
  · have : b = 1 := by linarith
    subst this
    linarith
  · rcases hb.eq_or_lt with rfl | hb_pos
    · have : a = 1 := by linarith
      subst this
      linarith
    · have h_ax : a * (x 0 + x 1) < a * c := mul_lt_mul_of_pos_left hx ha_pos
      have h_by : b * (y 0 + y 1) < b * c := mul_lt_mul_of_pos_left hy hb_pos
      have h_sum : a * (x 0 + x 1) + b * (y 0 + y 1) < c := by
        calc a * (x 0 + x 1) + b * (y 0 + y 1)
          _ < a * c + b * c := add_lt_add h_ax h_by
          _ = (a + b) * c := by ring
          _ = c := by rw [hab, one_mul]
      have h_eq : a * x 0 + b * y 0 + (a * x 1 + b * y 1) =
          a * (x 0 + x 1) + b * (y 0 + y 1) := by ring
      linarith

lemma mem_LShapeConvexHull_sum_lt {r R : ℝ}
    {y : Fin 2 → ℝ} (hy : y ∈ LShapeConvexHull r R) :
    y 0 + y 1 < r + R := by
  have h := convexHull_min LShape_subset_sum_lt (convex_halfspace_sum (r + R))
  exact h hy

lemma lshape_quadrant1_point {r R : ℝ} (hr : 0 < r) (hR : r < R)
    {y' : Fin 2 → ℝ} (hy' : y' ∈ LShapeConvexHull r R) :
    ∃ y ∈ LShape r R, ∃ δ > 0, ∀ ξ : Fin 2 → ℝ,
      0 ≤ ξ 0 → 0 ≤ ξ 1 → (y 0 - y' 0) * ξ 0 + (y 1 - y' 1) * ξ 1 ≤ -δ * (ξ 0 + ξ 1) := by
  have ⟨hy'0_pos, hy'0_R, hy'1_pos, hy'1_R⟩ := mem_LShapeConvexHull_bounds hR hy'
  let δ := min (y' 0 / 2) (min (y' 1 / 2) (r / 2))
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    positivity
  let y : Fin 2 → ℝ := fun _ => δ
  have hy_LS : y ∈ LShape r R := by
    unfold LShape
    left
    have hδ_lt_r : δ < r := by
      have : δ ≤ r / 2 := by
        dsimp [δ]
        exact min_le_of_right_le (min_le_right _ _)
      linarith
    have hδ_lt_R : δ < R := hδ_lt_r.trans hR
    exact ⟨hδ_pos, hδ_lt_r, hδ_pos, hδ_lt_R⟩
  refine ⟨y, hy_LS, δ, hδ_pos, ?_⟩
  intro ξ hξ0 hξ1
  have hy0_le : y 0 - y' 0 ≤ -δ := by
    dsimp [y, δ]
    have : min (y' 0 / 2) (min (y' 1 / 2) (r / 2)) ≤ y' 0 / 2 := min_le_left _ _
    linarith
  have hy1_le : y 1 - y' 1 ≤ -δ := by
    dsimp [y, δ]
    have : min (y' 0 / 2) (min (y' 1 / 2) (r / 2)) ≤ y' 1 / 2 :=
      min_le_of_right_le (min_le_left _ _)
    linarith
  calc (y 0 - y' 0) * ξ 0 + (y 1 - y' 1) * ξ 1
    _ ≤ (-δ) * ξ 0 + (-δ) * ξ 1 := by
      gcongr
    _ = -δ * (ξ 0 + ξ 1) := by ring

lemma lshape_quadrant2_point {r R : ℝ} (hr : 0 < r) (hR : r < R)
    {y' : Fin 2 → ℝ} (hy' : y' ∈ LShapeConvexHull r R) :
    ∃ y ∈ LShape r R, ∃ δ > 0, ∀ ξ : Fin 2 → ℝ,
      ξ 0 ≤ 0 → 0 ≤ ξ 1 → (y 0 - y' 0) * ξ 0 + (y 1 - y' 1) * ξ 1 ≤ -δ * (-ξ 0 + ξ 1) := by
  have ⟨hy'0_pos, hy'0_R, hy'1_pos, hy'1_R⟩ := mem_LShapeConvexHull_bounds hR hy'
  let δ := min ((R - y' 0) / 4) (min (y' 1 / 2) (r / 2))
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    have : 0 < R - y' 0 := by linarith
    positivity
  let y : Fin 2 → ℝ := ![y' 0 + 2 * δ, δ]
  have hy0_val : y 0 = y' 0 + 2 * δ := rfl
  have hy1_val : y 1 = δ := rfl
  have hy_LS : y ∈ LShape r R := by
    unfold LShape
    right
    have hδ_le1 : δ ≤ (R - y' 0) / 4 := min_le_left _ _
    have hδ_le2 : δ ≤ r / 2 := min_le_of_right_le (min_le_right _ _)
    have hy0_lt : y 0 < R := by
      rw [hy0_val]
      linarith
    have hy0_gt : 0 < y 0 := by
      rw [hy0_val]
      linarith
    have hy1_lt : y 1 < r := by
      rw [hy1_val]
      linarith
    exact ⟨hy0_gt, hy0_lt, hy1_val.symm ▸ hδ_pos, hy1_lt⟩
  refine ⟨y, hy_LS, δ, hδ_pos, ?_⟩
  intro ξ hξ0 hξ1
  have hy0_ge : δ ≤ y 0 - y' 0 := by
    rw [hy0_val]
    linarith
  have hy1_le : y 1 - y' 1 ≤ -δ := by
    rw [hy1_val]
    have : δ ≤ y' 1 / 2 := min_le_of_right_le (min_le_left _ _)
    linarith
  have h_term0 : (y 0 - y' 0) * ξ 0 ≤ δ * ξ 0 := by
    nlinarith
  have h_term1 : (y 1 - y' 1) * ξ 1 ≤ (-δ) * ξ 1 := by
    nlinarith
  calc (y 0 - y' 0) * ξ 0 + (y 1 - y' 1) * ξ 1
    _ ≤ δ * ξ 0 + (-δ) * ξ 1 := add_le_add h_term0 h_term1
    _ = -δ * (-ξ 0 + ξ 1) := by ring

lemma lshape_quadrant4_point {r R : ℝ} (hr : 0 < r) (hR : r < R)
    {y' : Fin 2 → ℝ} (hy' : y' ∈ LShapeConvexHull r R) :
    ∃ y ∈ LShape r R, ∃ δ > 0, ∀ ξ : Fin 2 → ℝ,
      0 ≤ ξ 0 → ξ 1 ≤ 0 → (y 0 - y' 0) * ξ 0 + (y 1 - y' 1) * ξ 1 ≤ -δ * (ξ 0 - ξ 1) := by
  have ⟨hy'0_pos, hy'0_R, hy'1_pos, hy'1_R⟩ := mem_LShapeConvexHull_bounds hR hy'
  let δ := min (y' 0 / 2) (min ((R - y' 1) / 4) (r / 2))
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    have : 0 < R - y' 1 := by linarith
    positivity
  let y : Fin 2 → ℝ := ![δ, y' 1 + 2 * δ]
  have hy0_val : y 0 = δ := rfl
  have hy1_val : y 1 = y' 1 + 2 * δ := rfl
  have hy_LS : y ∈ LShape r R := by
    unfold LShape
    left
    have hδ_le1 : δ ≤ r / 2 := min_le_of_right_le (min_le_right _ _)
    have hδ_le2 : δ ≤ (R - y' 1) / 4 := min_le_of_right_le (min_le_left _ _)
    have hy0_lt : y 0 < r := by
      rw [hy0_val]
      linarith
    have hy1_gt : 0 < y 1 := by
      rw [hy1_val]
      linarith
    have hy1_lt : y 1 < R := by
      rw [hy1_val]
      linarith
    exact ⟨hy0_val.symm ▸ hδ_pos, hy0_lt, hy1_gt, hy1_lt⟩
  refine ⟨y, hy_LS, δ, hδ_pos, ?_⟩
  intro ξ hξ0 hξ1
  have hy0_le : y 0 - y' 0 ≤ -δ := by
    rw [hy0_val]
    have : δ ≤ y' 0 / 2 := min_le_left _ _
    linarith
  have hy1_ge : δ ≤ y 1 - y' 1 := by
    rw [hy1_val]
    linarith
  have h_term0 : (y 0 - y' 0) * ξ 0 ≤ (-δ) * ξ 0 := by
    nlinarith
  have h_term1 : (y 1 - y' 1) * ξ 1 ≤ δ * ξ 1 := by
    nlinarith
  calc (y 0 - y' 0) * ξ 0 + (y 1 - y' 1) * ξ 1
    _ ≤ (-δ) * ξ 0 + δ * ξ 1 := add_le_add h_term0 h_term1
    _ = -δ * (ξ 0 - ξ 1) := by ring

lemma lshape_quadrant3_point {r R : ℝ} (hr : 0 < r) (hR : r < R)
    {y' : Fin 2 → ℝ} (hy' : y' ∈ LShapeConvexHull r R) :
    ∃ y₁ ∈ LShape r R, ∃ y₂ ∈ LShape r R, ∃ δ > 0, ∀ ξ : Fin 2 → ℝ,
      ξ 0 ≤ 0 → ξ 1 ≤ 0 →
        ((y₁ 0 - y' 0) * ξ 0 + (y₁ 1 - y' 1) * ξ 1 ≤ -δ * (-ξ 0 - ξ 1) ∨
         (y₂ 0 - y' 0) * ξ 0 + (y₂ 1 - y' 1) * ξ 1 ≤ -δ * (-ξ 0 - ξ 1)) := by
  have ⟨hy'0_pos, hy'0_R, hy'1_pos, hy'1_R⟩ := mem_LShapeConvexHull_bounds hR hy'
  have h_sum := mem_LShapeConvexHull_sum_lt hy'
  let rem := r + R - (y' 0 + y' 1)
  have h_rem_pos : 0 < rem := by linarith
  have h_rem_eq : y' 0 + y' 1 = r + R - rem := by dsimp [rem]; ring
  let ε := min (rem / 8) (min ((R - y' 0) / 4) (min ((R - y' 1) / 4) (r / 6)))
  have hε_pos : 0 < ε := by
    dsimp [ε]
    have : 0 < R - y' 0 := by linarith
    have : 0 < R - y' 1 := by linarith
    positivity
  have hε_rem : 4 * ε ≤ rem := by
    have : ε ≤ rem / 8 := min_le_left _ _
    linarith
  have hε_R0 : 2 * ε ≤ R - y' 0 := by
    have : ε ≤ (R - y' 0) / 4 := min_le_of_right_le (min_le_left _ _)
    linarith
  have hε_R1 : 2 * ε ≤ R - y' 1 := by
    have : ε ≤ (R - y' 1) / 4 := min_le_of_right_le (min_le_of_right_le (min_le_left _ _))
    linarith
  have hε_r : 3 * ε ≤ r := by
    have : ε ≤ r / 6 := min_le_of_right_le (min_le_of_right_le (min_le_right _ _))
    linarith
  let y₁ : Fin 2 → ℝ := ![r - 2 * ε, R - ε]
  let y₂ : Fin 2 → ℝ := ![R - ε, r - 2 * ε]
  have hy1_LS : y₁ ∈ LShape r R := by
    unfold LShape
    left
    dsimp [y₁]
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hy2_LS : y₂ ∈ LShape r R := by
    unfold LShape
    right
    dsimp [y₂]
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  let δ := ε / 2
  have hδ_pos : 0 < δ := by dsimp [δ]; linarith
  refine ⟨y₁, hy1_LS, y₂, hy2_LS, δ, hδ_pos, ?_⟩
  intro ξ hξ0 hξ1
  let u0 := -ξ 0
  let u1 := -ξ 1
  have hu0 : 0 ≤ u0 := by dsimp [u0]; linarith
  have hu1 : 0 ≤ u1 := by dsimp [u1]; linarith
  by_cases h_order : u0 ≤ u1
  · left
    have h_diff1 : ε ≤ y₁ 1 - y' 1 := by
      change ε ≤ R - ε - y' 1
      linarith
    have h_sum1 : ε ≤ (y₁ 0 - y' 0) + (y₁ 1 - y' 1) := by
      change ε ≤ (r - 2 * ε - y' 0) + (R - ε - y' 1)
      linarith
    have h_ineq : δ * (u0 + u1) ≤ (y₁ 0 - y' 0) * u0 + (y₁ 1 - y' 1) * u1 := by
      calc δ * (u0 + u1)
        _ ≤ δ * (2 * u1) := by
          dsimp [δ]
          nlinarith
        _ = ε * u1 := by dsimp [δ]; ring
        _ = ((y₁ 0 - y' 0) + (y₁ 1 - y' 1)) * u0 + (y₁ 1 - y' 1) * (u1 - u0) -
            (((y₁ 0 - y' 0) + (y₁ 1 - y' 1)) - ε) * u0 - ((y₁ 1 - y' 1) - ε) * (u1 - u0) := by ring
        _ ≤ ((y₁ 0 - y' 0) + (y₁ 1 - y' 1)) * u0 + (y₁ 1 - y' 1) * (u1 - u0) := by
          have : 0 ≤ (((y₁ 0 - y' 0) + (y₁ 1 - y' 1)) - ε) * u0 := by nlinarith
          have : 0 ≤ ((y₁ 1 - y' 1) - ε) * (u1 - u0) := by nlinarith
          linarith
        _ = (y₁ 0 - y' 0) * u0 + (y₁ 1 - y' 1) * u1 := by ring
    dsimp [u0, u1] at h_ineq
    linarith
  · right
    have hu_le : u1 ≤ u0 := le_of_not_ge h_order
    have h_diff0 : ε ≤ y₂ 0 - y' 0 := by
      change ε ≤ R - ε - y' 0
      linarith
    have h_sum2 : ε ≤ (y₂ 0 - y' 0) + (y₂ 1 - y' 1) := by
      change ε ≤ (R - ε - y' 0) + (r - 2 * ε - y' 1)
      linarith
    have h_ineq : δ * (u0 + u1) ≤ (y₂ 0 - y' 0) * u0 + (y₂ 1 - y' 1) * u1 := by
      calc δ * (u0 + u1)
        _ ≤ δ * (2 * u0) := by
          dsimp [δ]
          nlinarith
        _ = ε * u0 := by dsimp [δ]; ring
        _ = ((y₂ 0 - y' 0) + (y₂ 1 - y' 1)) * u1 + (y₂ 0 - y' 0) * (u0 - u1) -
            (((y₂ 0 - y' 0) + (y₂ 1 - y' 1)) - ε) * u1 - ((y₂ 0 - y' 0) - ε) * (u0 - u1) := by ring
        _ ≤ ((y₂ 0 - y' 0) + (y₂ 1 - y' 1)) * u1 + (y₂ 0 - y' 0) * (u0 - u1) := by
          have : 0 ≤ (((y₂ 0 - y' 0) + (y₂ 1 - y' 1)) - ε) * u1 := by nlinarith
          have : 0 ≤ ((y₂ 0 - y' 0) - ε) * (u0 - u1) := by nlinarith
          linarith
        _ = (y₂ 0 - y' 0) * u0 + (y₂ 1 - y' 1) * u1 := by ring
    dsimp [u0, u1] at h_ineq
    linarith

lemma bochner_c_eps_local_exp_decay (r R : ℝ) (hr : 0 < r) (hR : r < R)
    (f : (Fin 2 → ℂ) → ℂ) (hf_holo : DifferentiableOn ℂ f (TubeDomain (LShape r R)))
    (hf_bound : ∃ M : ℝ, ∀ z : Fin 2 → ℂ, ‖f z‖ ≤ M)
    (ε : ℝ) (hε : 0 < ε)
    (y' : Fin 2 → ℝ) (hy' : y' ∈ LShapeConvexHull r R) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ ∀ ξ : Fin 2 → ℝ,
      ‖bochner_fourier_transform_eps f ε (fun _ => r/2) ξ *
        ↑(Real.exp ((r/2) * ξ 0 + (r/2) * ξ 1))‖ *
        Real.exp (-(y' 0 * ξ 0 + y' 1 * ξ 1)) ≤
      C * Real.exp (-δ * (|ξ 0| + |ξ 1|)) := by
  rcases lshape_quadrant1_point hr hR hy' with ⟨y1, hy1, δ1, hδ1_pos, hq1⟩
  rcases lshape_quadrant2_point hr hR hy' with ⟨y2, hy2, δ2, hδ2_pos, hq2⟩
  rcases lshape_quadrant4_point hr hR hy' with ⟨y4, hy4, δ4, hδ4_pos, hq4⟩
  rcases lshape_quadrant3_point hr hR hy' with ⟨y3a, hy3a, y3b, hy3b, δ3, hδ3_pos, hq3⟩
  rcases bochner_c_eps_bound_of_y r R hr hR f hf_holo hf_bound ε hε y1 hy1 with
    ⟨C1, hC1_nonneg, h_bd1⟩
  rcases bochner_c_eps_bound_of_y r R hr hR f hf_holo hf_bound ε hε y2 hy2 with
    ⟨C2, hC2_nonneg, h_bd2⟩
  rcases bochner_c_eps_bound_of_y r R hr hR f hf_holo hf_bound ε hε y4 hy4 with
    ⟨C4, hC4_nonneg, h_bd4⟩
  rcases bochner_c_eps_bound_of_y r R hr hR f hf_holo hf_bound ε hε y3a hy3a with
    ⟨C3a, hC3a_nonneg, h_bd3a⟩
  rcases bochner_c_eps_bound_of_y r R hr hR f hf_holo hf_bound ε hε y3b hy3b with
    ⟨C3b, hC3b_nonneg, h_bd3b⟩
  let C := max C1 (max C2 (max C4 (max C3a C3b)))
  have hC_nonneg : 0 ≤ C := le_trans hC1_nonneg (le_max_left _ _)
  let δ := min δ1 (min δ2 (min δ4 δ3))
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    positivity
  have hC_ge1 : C1 ≤ C := le_max_left _ _
  have hC_ge2 : C2 ≤ C := le_trans (le_max_left _ _) (le_max_right _ _)
  have hC_ge4 : C4 ≤ C :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hC_ge3a : C3a ≤ C :=
    le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _)))
  have hC_ge3b : C3b ≤ C :=
    le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
      (le_trans (le_max_right _ _) (le_max_right _ _)))
  refine ⟨C, δ, hC_nonneg, hδ_pos, ?_⟩
  intro ξ
  let c_norm :=
    ‖bochner_fourier_transform_eps f ε (fun _ => r/2) ξ * ↑(Real.exp ((r/2) * ξ 0 + (r/2) * ξ 1))‖
  have h_combine (y : Fin 2 → ℝ) (Cy : ℝ) (hCy : Cy ≤ C)
      (h_bdy : c_norm ≤ Cy * Real.exp (y 0 * ξ 0 + y 1 * ξ 1))
      (h_geom : (y 0 - y' 0) * ξ 0 + (y 1 - y' 1) * ξ 1 ≤ -δ * (|ξ 0| + |ξ 1|)) :
      c_norm * Real.exp (-(y' 0 * ξ 0 + y' 1 * ξ 1)) ≤ C * Real.exp (-δ * (|ξ 0| + |ξ 1|)) := by
    calc c_norm * Real.exp (-(y' 0 * ξ 0 + y' 1 * ξ 1))
      _ ≤ (Cy * Real.exp (y 0 * ξ 0 + y 1 * ξ 1)) * Real.exp (-(y' 0 * ξ 0 + y' 1 * ξ 1)) := by
        nlinarith [Real.exp_pos (-(y' 0 * ξ 0 + y' 1 * ξ 1))]
      _ = Cy * (Real.exp (y 0 * ξ 0 + y 1 * ξ 1) * Real.exp (-(y' 0 * ξ 0 + y' 1 * ξ 1))) := by ring
      _ = Cy * Real.exp ((y 0 - y' 0) * ξ 0 + (y 1 - y' 1) * ξ 1) := by
        congr 1
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ C * Real.exp (-δ * (|ξ 0| + |ξ 1|)) := by
        have h_exp : Real.exp ((y 0 - y' 0) * ξ 0 + (y 1 - y' 1) * ξ 1) ≤
            Real.exp (-δ * (|ξ 0| + |ξ 1|)) :=
          Real.exp_le_exp.mpr h_geom
        exact mul_le_mul hCy h_exp (Real.exp_pos _).le hC_nonneg
  by_cases h0 : 0 ≤ ξ 0
  · by_cases h1 : 0 ≤ ξ 1
    · have habs0 : |ξ 0| = ξ 0 := abs_of_nonneg h0
      have habs1 : |ξ 1| = ξ 1 := abs_of_nonneg h1
      have hg : (y1 0 - y' 0) * ξ 0 + (y1 1 - y' 1) * ξ 1 ≤ -δ * (|ξ 0| + |ξ 1|) := by
        rw [habs0, habs1]
        have hq := hq1 ξ h0 h1
        have : -δ1 * (ξ 0 + ξ 1) ≤ -δ * (ξ 0 + ξ 1) := by
          have : δ ≤ δ1 := min_le_left _ _
          nlinarith
        linarith
      exact h_combine y1 C1 hC_ge1 (h_bd1 ξ) hg
    · have h1' : ξ 1 ≤ 0 := le_of_not_ge h1
      have habs0 : |ξ 0| = ξ 0 := abs_of_nonneg h0
      have habs1 : |ξ 1| = -ξ 1 := abs_of_nonpos h1'
      have hg : (y4 0 - y' 0) * ξ 0 + (y4 1 - y' 1) * ξ 1 ≤ -δ * (|ξ 0| + |ξ 1|) := by
        have h_sum : |ξ 0| + |ξ 1| = ξ 0 - ξ 1 := by linarith
        rw [h_sum]
        have hq := hq4 ξ h0 h1'
        have : -δ4 * (ξ 0 - ξ 1) ≤ -δ * (ξ 0 - ξ 1) := by
          have : δ ≤ δ4 :=
            le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
          nlinarith
        linarith
      exact h_combine y4 C4 hC_ge4 (h_bd4 ξ) hg
  · have h0' : ξ 0 ≤ 0 := le_of_not_ge h0
    by_cases h1 : 0 ≤ ξ 1
    · have habs0 : |ξ 0| = -ξ 0 := abs_of_nonpos h0'
      have habs1 : |ξ 1| = ξ 1 := abs_of_nonneg h1
      have hg : (y2 0 - y' 0) * ξ 0 + (y2 1 - y' 1) * ξ 1 ≤ -δ * (|ξ 0| + |ξ 1|) := by
        have h_sum : |ξ 0| + |ξ 1| = -ξ 0 + ξ 1 := by linarith
        rw [h_sum]
        have hq := hq2 ξ h0' h1
        have : -δ2 * (-ξ 0 + ξ 1) ≤ -δ * (-ξ 0 + ξ 1) := by
          have : δ ≤ δ2 := le_trans (min_le_right _ _) (min_le_left _ _)
          nlinarith
        linarith
      exact h_combine y2 C2 hC_ge2 (h_bd2 ξ) hg
    · have h1' : ξ 1 ≤ 0 := le_of_not_ge h1
      have habs0 : |ξ 0| = -ξ 0 := abs_of_nonpos h0'
      have habs1 : |ξ 1| = -ξ 1 := abs_of_nonpos h1'
      have h_sum : |ξ 0| + |ξ 1| = -ξ 0 - ξ 1 := by linarith
      rcases hq3 ξ h0' h1' with hq3a | hq3b
      · have hg : (y3a 0 - y' 0) * ξ 0 + (y3a 1 - y' 1) * ξ 1 ≤ -δ * (|ξ 0| + |ξ 1|) := by
          rw [h_sum]
          have : -δ3 * (-ξ 0 - ξ 1) ≤ -δ * (-ξ 0 - ξ 1) := by
            have : δ ≤ δ3 :=
              le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
            nlinarith
          linarith
        exact h_combine y3a C3a hC_ge3a (h_bd3a ξ) hg
      · have hg : (y3b 0 - y' 0) * ξ 0 + (y3b 1 - y' 1) * ξ 1 ≤ -δ * (|ξ 0| + |ξ 1|) := by
          rw [h_sum]
          have : -δ3 * (-ξ 0 - ξ 1) ≤ -δ * (-ξ 0 - ξ 1) := by
            have : δ ≤ δ3 :=
              le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
            nlinarith
          linarith
        exact h_combine y3b C3b hC_ge3b (h_bd3b ξ) hg

lemma exp_im_diff_le {z w : Fin 2 → ℂ} {η : ℝ} (hw : w ∈ Metric.closedBall z η) (ξ : Fin 2 → ℝ) :
    -(w 0).im * ξ 0 - (w 1).im * ξ 1 ≤
      -(z 0).im * ξ 0 - (z 1).im * ξ 1 + η * (|ξ 0| + |ξ 1|) := by
  have hw_dist : ‖w - z‖ ≤ η := by
    rw [← dist_eq_norm]
    exact Metric.mem_closedBall.mp hw
  have h_im0 : |(w 0).im - (z 0).im| ≤ η := by
    calc |(w 0).im - (z 0).im|
      _ = |(w 0 - z 0).im| := by rw [sub_im]
      _ ≤ ‖w 0 - z 0‖ := abs_im_le_norm _
      _ ≤ ‖w - z‖ := norm_le_pi_norm (w - z) 0
      _ ≤ η := hw_dist
  have h_im1 : |(w 1).im - (z 1).im| ≤ η := by
    calc |(w 1).im - (z 1).im|
      _ = |(w 1 - z 1).im| := by rw [sub_im]
      _ ≤ ‖w 1 - z 1‖ := abs_im_le_norm _
      _ ≤ ‖w - z‖ := norm_le_pi_norm (w - z) 1
      _ ≤ η := hw_dist
  have h_term0 : (-(w 0).im + (z 0).im) * ξ 0 ≤ η * |ξ 0| := by
    have : -(w 0).im + (z 0).im = -((w 0).im - (z 0).im) := by ring
    rw [this]
    calc -((w 0).im - (z 0).im) * ξ 0
      _ ≤ |-((w 0).im - (z 0).im) * ξ 0| := le_abs_self _
      _ = |(w 0).im - (z 0).im| * |ξ 0| := by rw [abs_mul, abs_neg]
      _ ≤ η * |ξ 0| := mul_le_mul_of_nonneg_right h_im0 (abs_nonneg _)
  have h_term1 : (-(w 1).im + (z 1).im) * ξ 1 ≤ η * |ξ 1| := by
    have : -(w 1).im + (z 1).im = -((w 1).im - (z 1).im) := by ring
    rw [this]
    calc -((w 1).im - (z 1).im) * ξ 1
      _ ≤ |-((w 1).im - (z 1).im) * ξ 1| := le_abs_self _
      _ = |(w 1).im - (z 1).im| * |ξ 1| := by rw [abs_mul, abs_neg]
      _ ≤ η * |ξ 1| := mul_le_mul_of_nonneg_right h_im1 (abs_nonneg _)
  calc -(w 0).im * ξ 0 - (w 1).im * ξ 1
    _ = -(z 0).im * ξ 0 - (z 1).im * ξ 1 +
        ((-(w 0).im + (z 0).im) * ξ 0 + (-(w 1).im + (z 1).im) * ξ 1) := by ring
    _ ≤ -(z 0).im * ξ 0 - (z 1).im * ξ 1 + (η * |ξ 0| + η * |ξ 1|) := by linarith
    _ = -(z 0).im * ξ 0 - (z 1).im * ξ 1 + η * (|ξ 0| + |ξ 1|) := by ring

lemma integrable_exp_neg_abs {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : ℝ => Real.exp (-c * |x|)) volume := by
  have h_Ioi : IntegrableOn (fun x : ℝ => Real.exp (-c * x)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hc) 0
  have h1 : IntegrableOn (fun x : ℝ => Real.exp (-c * |x|)) (Ioi 0) := by
    refine h_Ioi.congr_fun (fun x hx => ?_) measurableSet_Ioi
    have : |x| = x := abs_of_pos (mem_Ioi.mp hx)
    rw [this]
  have h_Iic : IntegrableOn (fun x : ℝ => Real.exp (c * x)) (Iic 0) :=
    integrableOn_exp_mul_Iic hc 0
  have h2 : IntegrableOn (fun x : ℝ => Real.exp (-c * |x|)) (Iic 0) := by
    refine h_Iic.congr_fun (fun x hx => ?_) measurableSet_Iic
    have : |x| = -x := abs_of_nonpos (mem_Iic.mp hx)
    rw [this, show -c * -x = c * x by ring]
  have h_union : IntegrableOn (fun x : ℝ => Real.exp (-c * |x|)) (Iic 0 ∪ Ioi 0) :=
    h2.union h1
  have h_univ : (Iic (0 : ℝ) ∪ Ioi (0 : ℝ)) = univ := Iic_union_Ioi
  rw [h_univ, integrableOn_univ] at h_union
  exact h_union

lemma integrable_exp_neg_abs_2d (c : ℝ) (hc : 0 < c) :
    Integrable (fun x : Fin 2 → ℝ => Real.exp (-c * (|x 0| + |x 1|))) := by
  have h_eq : (fun x : Fin 2 → ℝ => Real.exp (-c * (|x 0| + |x 1|))) =
      (fun p : ℝ × ℝ => Real.exp (-c * |p.1|) * Real.exp (-c * |p.2|)) ∘
      (⇑MeasurableEquiv.finTwoArrow) := by
    ext x
    simp only [Function.comp_apply, MeasurableEquiv.finTwoArrow_apply]
    rw [← Real.exp_add]
    congr 1
    ring
  rw [h_eq]
  have h_pres := volume_preserving_finTwoArrow ℝ
  have h_emb := (@MeasurableEquiv.finTwoArrow ℝ _).measurableEmbedding
  rw [h_pres.integrable_comp_emb h_emb]
  have h1 : Integrable (fun x : ℝ => Real.exp (-c * |x|)) volume := integrable_exp_neg_abs hc
  have h_prod :
      Integrable (fun p : ℝ × ℝ => Real.exp (-c * |p.1|) * Real.exp (-c * |p.2|)) volume :=
    Integrable.mul_prod h1 h1
  exact h_prod

lemma poly_le_exp_half (c : ℝ) (hc : 0 < c) (x : ℝ) :
    |x| + 1 ≤ (2 / c + 1) * Real.exp (c / 2 * |x|) := by
  have h_exp : c / 2 * |x| ≤ Real.exp (c / 2 * |x|) := by
    have : 0 ≤ c / 2 * |x| := by positivity
    linarith [Real.add_one_le_exp (c / 2 * |x|)]
  have h_pos : 0 < c / 2 := by linarith
  have h_one : 1 ≤ Real.exp (c / 2 * |x|) := by
    have : 0 ≤ c / 2 * |x| := by positivity
    exact Real.one_le_exp this
  have h_div : |x| ≤ (2 / c) * Real.exp (c / 2 * |x|) := by
    have h_cancel : (c / 2) * ((2 / c) * Real.exp (c / 2 * |x|)) = Real.exp (c / 2 * |x|) := by
      have : (c / 2) * (2 / c) = 1 := by field_simp
      calc (c / 2) * ((2 / c) * Real.exp (c / 2 * |x|))
        _ = ((c / 2) * (2 / c)) * Real.exp (c / 2 * |x|) := by ring
        _ = 1 * Real.exp (c / 2 * |x|) := by rw [this]
        _ = Real.exp (c / 2 * |x|) := by ring
    have : (c / 2) * |x| ≤ (c / 2) * ((2 / c) * Real.exp (c / 2 * |x|)) := by
      rw [h_cancel]
      exact h_exp
    exact le_of_mul_le_mul_left this h_pos
  have : (2 / c + 1) * Real.exp (c / 2 * |x|) =
      (2 / c) * Real.exp (c / 2 * |x|) + Real.exp (c / 2 * |x|) := by ring
  rw [this]
  linarith

lemma exp_poly_2d_le (c : ℝ) (hc : 0 < c) (ξ : Fin 2 → ℝ) :
    Real.exp (-c * (|ξ 0| + |ξ 1|)) * (|ξ 0| + |ξ 1| + 1) ≤
      (2 / c + 1) ^ 2 * Real.exp (-(c / 2) * (|ξ 0| + |ξ 1|)) := by
  have h0 := poly_le_exp_half c hc (ξ 0)
  have h1 := poly_le_exp_half c hc (ξ 1)
  have h_poly : |ξ 0| + |ξ 1| + 1 ≤ (|ξ 0| + 1) * (|ξ 1| + 1) := by
    nlinarith [abs_nonneg (ξ 0), abs_nonneg (ξ 1)]
  have h_prod : (|ξ 0| + 1) * (|ξ 1| + 1) ≤
      ((2 / c + 1) * Real.exp (c / 2 * |ξ 0|)) * ((2 / c + 1) * Real.exp (c / 2 * |ξ 1|)) := by
    have : 0 ≤ |ξ 0| + 1 := by positivity
    have : 0 ≤ |ξ 1| + 1 := by positivity
    gcongr
  have h_comb : |ξ 0| + |ξ 1| + 1 ≤ (2 / c + 1) ^ 2 * Real.exp (c / 2 * (|ξ 0| + |ξ 1|)) := by
    calc |ξ 0| + |ξ 1| + 1
      _ ≤ ((2 / c + 1) * Real.exp (c / 2 * |ξ 0|)) * ((2 / c + 1) * Real.exp (c / 2 * |ξ 1|)) :=
        h_poly.trans h_prod
      _ = (2 / c + 1) ^ 2 * (Real.exp (c / 2 * |ξ 0|) * Real.exp (c / 2 * |ξ 1|)) := by ring
      _ = (2 / c + 1) ^ 2 * Real.exp (c / 2 * |ξ 0| + c / 2 * |ξ 1|) := by rw [← Real.exp_add]
      _ = (2 / c + 1) ^ 2 * Real.exp (c / 2 * (|ξ 0| + |ξ 1|)) := by ring_nf
  calc Real.exp (-c * (|ξ 0| + |ξ 1|)) * (|ξ 0| + |ξ 1| + 1)
    _ ≤ Real.exp (-c * (|ξ 0| + |ξ 1|)) *
        ((2 / c + 1) ^ 2 * Real.exp (c / 2 * (|ξ 0| + |ξ 1|))) := by
      gcongr
    _ = (2 / c + 1) ^ 2 *
        (Real.exp (-c * (|ξ 0| + |ξ 1|)) * Real.exp (c / 2 * (|ξ 0| + |ξ 1|))) := by ring
    _ = (2 / c + 1) ^ 2 *
        Real.exp (-c * (|ξ 0| + |ξ 1|) + c / 2 * (|ξ 0| + |ξ 1|)) := by rw [← Real.exp_add]
    _ = (2 / c + 1) ^ 2 * Real.exp (-(c / 2) * (|ξ 0| + |ξ 1|)) := by ring_nf

lemma integrable_exp_neg_abs_poly_2d (c : ℝ) (hc : 0 < c) :
    Integrable (fun x : Fin 2 → ℝ => Real.exp (-c * (|x 0| + |x 1|)) * (|x 0| + |x 1| + 1)) := by
  have h_bound : Integrable
      (fun x : Fin 2 → ℝ => (2 / c + 1) ^ 2 * Real.exp (-(c / 2) * (|x 0| + |x 1|))) :=
    (integrable_exp_neg_abs_2d (c / 2) (by linarith)).const_mul _
  have h_cont :
      Continuous (fun x : Fin 2 → ℝ => Real.exp (-c * (|x 0| + |x 1|)) * (|x 0| + |x 1| + 1)) := by
    apply Continuous.mul
    · apply Real.continuous_exp.comp
      apply continuous_const.mul
      apply Continuous.add
      · exact (continuous_apply 0).abs
      · exact (continuous_apply 1).abs
    · apply Continuous.add
      · apply Continuous.add
        · exact (continuous_apply 0).abs
        · exact (continuous_apply 1).abs
      · exact continuous_const
  have h_meas : AEStronglyMeasurable
      (fun x : Fin 2 → ℝ => Real.exp (-c * (|x 0| + |x 1|)) * (|x 0| + |x 1| + 1)) volume :=
    h_cont.aestronglyMeasurable
  have h_le : ∀ᵐ x : Fin 2 → ℝ,
      ‖Real.exp (-c * (|x 0| + |x 1|)) * (|x 0| + |x 1| + 1)‖ ≤
        (2 / c + 1) ^ 2 * Real.exp (-(c / 2) * (|x 0| + |x 1|)) := by
    apply ae_of_all
    intro x
    have h_nonneg : 0 ≤ Real.exp (-c * (|x 0| + |x 1|)) * (|x 0| + |x 1| + 1) := by positivity
    rw [Real.norm_of_nonneg h_nonneg]
    exact exp_poly_2d_le c hc x
  exact Integrable.mono' h_bound h_meas h_le

lemma fourier_inversion_integrand_cancel (x y ξ : Fin 2 → ℝ) :
    (↑(Real.exp (y 0 * ξ 0 + y 1 * ξ 1)) : ℂ) *
      Complex.exp (I * ((↑(x 0) + I * ↑(y 0)) * ↑(ξ 0) + (↑(x 1) + I * ↑(y 1)) * ↑(ξ 1))) =
    Complex.exp (I * (↑(x 0) * ↑(ξ 0) + ↑(x 1) * ↑(ξ 1))) := by
  have h_exp_real : (↑(Real.exp (y 0 * ξ 0 + y 1 * ξ 1)) : ℂ) =
      Complex.exp (↑(y 0 * ξ 0 + y 1 * ξ 1)) :=
    ofReal_exp (y 0 * ξ 0 + y 1 * ξ 1)
  rw [h_exp_real, ← Complex.exp_add]
  congr 1
  push_cast
  have h_I2 : I ^ 2 = -1 := I_sq
  linear_combination (↑(y 0) * ↑(ξ 0) + ↑(y 1) * ↑(ξ 1)) * h_I2

noncomputable def bochner_F_eps (f : (Fin 2 → ℂ) → ℂ) (ε r _R : ℝ) (z : Fin 2 → ℂ) : ℂ :=
  (2 * Real.pi)⁻¹ * (2 * Real.pi)⁻¹ * ∫ (ξ : Fin 2 → ℝ),
    (bochner_fourier_transform_eps f ε (fun _ => r/2) ξ * Real.exp ((r/2) * ξ 0 + (r/2) * ξ 1)) *
    Complex.exp (I * (z 0 * ↑(ξ 0) + z 1 * ↑(ξ 1)))

lemma bochner_fourier_integrand_differentiable (c : (Fin 2 → ℝ) → ℂ) (ξ : Fin 2 → ℝ) :
    Differentiable ℂ
      (fun z : Fin 2 → ℂ => c ξ * Complex.exp (I * (z 0 * ↑(ξ 0) + z 1 * ↑(ξ 1)))) := by
  apply Differentiable.mul (differentiable_const _)
  apply Differentiable.comp Complex.differentiable_exp
  apply Differentiable.mul (differentiable_const _)
  apply Differentiable.add
  · exact (differentiable_apply 0).mul (differentiable_const _)
  · exact (differentiable_apply 1).mul (differentiable_const _)

lemma fourier_integrand_deriv0 (c : (Fin 2 → ℝ) → ℂ) (ξ : Fin 2 → ℝ) (z : Fin 2 → ℂ) :
    HasDerivAt (fun w : ℂ => c ξ * Complex.exp (I * (w * ↑(ξ 0) + z 1 * ↑(ξ 1))))
      (c ξ * (Complex.exp (I * (z 0 * ↑(ξ 0) + z 1 * ↑(ξ 1))) * (I * ↑(ξ 0)))) (z 0) := by
  have h1 : HasDerivAt (fun w : ℂ => I * (w * ↑(ξ 0) + z 1 * ↑(ξ 1))) (I * ↑(ξ 0)) (z 0) := by
    have h_inner : HasDerivAt (fun w : ℂ => w * ↑(ξ 0) + z 1 * ↑(ξ 1)) (1 * ↑(ξ 0) + 0) (z 0) := by
      apply HasDerivAt.add
      · exact (hasDerivAt_id (z 0)).mul_const (ξ 0 : ℂ)
      · exact hasDerivAt_const (z 0) (z 1 * (ξ 1 : ℂ))
    have h_inner2 : HasDerivAt (fun w : ℂ => w * ↑(ξ 0) + z 1 * ↑(ξ 1)) (ξ 0 : ℂ) (z 0) := by
      simpa using h_inner
    have h_mul := h_inner2.const_mul I
    simpa [mul_comm] using h_mul
  have h_exp := h1.cexp
  exact h_exp.const_mul (c ξ)

lemma fourier_integrand_deriv1 (c : (Fin 2 → ℝ) → ℂ) (ξ : Fin 2 → ℝ) (z : Fin 2 → ℂ) :
    HasDerivAt (fun w : ℂ => c ξ * Complex.exp (I * (z 0 * ↑(ξ 0) + w * ↑(ξ 1))))
      (c ξ * (Complex.exp (I * (z 0 * ↑(ξ 0) + z 1 * ↑(ξ 1))) * (I * ↑(ξ 1)))) (z 1) := by
  have h1 : HasDerivAt (fun w : ℂ => I * (z 0 * ↑(ξ 0) + w * ↑(ξ 1))) (I * ↑(ξ 1)) (z 1) := by
    have h_inner : HasDerivAt (fun w : ℂ => z 0 * ↑(ξ 0) + w * ↑(ξ 1)) (0 + 1 * ↑(ξ 1)) (z 1) := by
      apply HasDerivAt.add
      · exact hasDerivAt_const (z 1) (z 0 * (ξ 0 : ℂ))
      · exact (hasDerivAt_id (z 1)).mul_const (ξ 1 : ℂ)
    have h_inner2 : HasDerivAt (fun w : ℂ => z 0 * ↑(ξ 0) + w * ↑(ξ 1)) (ξ 1 : ℂ) (z 1) := by
      simpa using h_inner
    have h_mul := h_inner2.const_mul I
    simpa [mul_comm] using h_mul
  have h_exp := h1.cexp
  exact h_exp.const_mul (c ξ)

lemma bochner_fourier_integral_deriv0_of_bound (c : (Fin 2 → ℝ) → ℂ) (z : Fin 2 → ℂ)
    (bound : (Fin 2 → ℝ) → ℝ) (s : Set ℂ) (hs : s ∈ 𝓝 (z 0))
    (hF_meas : ∀ᶠ (w : ℂ) in 𝓝 (z 0),
      AEStronglyMeasurable (fun ξ => c ξ * Complex.exp (I * (w * ↑(ξ 0) + z 1 * ↑(ξ 1)))) volume)
    (hF_int : Integrable (fun ξ => c ξ * Complex.exp (I * (z 0 * ↑(ξ 0) + z 1 * ↑(ξ 1)))) volume)
    (hF'_meas : AEStronglyMeasurable
      (fun ξ => c ξ * (Complex.exp (I * (z 0 * ↑(ξ 0) + z 1 * ↑(ξ 1))) * (I * ↑(ξ 0)))) volume)
    (h_bound : ∀ᵐ (ξ : Fin 2 → ℝ), ∀ w ∈ s,
      ‖c ξ * (Complex.exp (I * (w * ↑(ξ 0) + z 1 * ↑(ξ 1))) * (I * ↑(ξ 0)))‖ ≤ bound ξ)
    (bound_int : Integrable bound volume) :
    HasDerivAt (fun w : ℂ => ∫ (ξ : Fin 2 → ℝ), c ξ * Complex.exp (I * (w * ↑(ξ 0) + z 1 * ↑(ξ 1))))
      (∫ (ξ : Fin 2 → ℝ),
        c ξ * (Complex.exp (I * (z 0 * ↑(ξ 0) + z 1 * ↑(ξ 1))) * (I * ↑(ξ 0)))) (z 0) := by
  have h_diff : ∀ᵐ (ξ : Fin 2 → ℝ), ∀ w ∈ s,
      HasDerivAt (fun w' => c ξ * Complex.exp (I * (w' * ↑(ξ 0) + z 1 * ↑(ξ 1))))
        (c ξ * (Complex.exp (I * (w * ↑(ξ 0) + z 1 * ↑(ξ 1))) * (I * ↑(ξ 0)))) w := by
    apply ae_of_all
    intro ξ w _hw
    exact fourier_integrand_deriv0 c ξ ![w, z 1]
  have h_res := hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hF_meas hF_int hF'_meas
    h_bound bound_int h_diff
  exact h_res.2

lemma bochner_fourier_integral_deriv1_of_bound (c : (Fin 2 → ℝ) → ℂ) (z : Fin 2 → ℂ)
    (bound : (Fin 2 → ℝ) → ℝ) (s : Set ℂ) (hs : s ∈ 𝓝 (z 1))
    (hF_meas : ∀ᶠ (w : ℂ) in 𝓝 (z 1),
      AEStronglyMeasurable (fun ξ => c ξ * Complex.exp (I * (z 0 * ↑(ξ 0) + w * ↑(ξ 1)))) volume)
    (hF_int : Integrable (fun ξ => c ξ * Complex.exp (I * (z 0 * ↑(ξ 0) + z 1 * ↑(ξ 1)))) volume)
    (hF'_meas : AEStronglyMeasurable
      (fun ξ => c ξ * (Complex.exp (I * (z 0 * ↑(ξ 0) + z 1 * ↑(ξ 1))) * (I * ↑(ξ 1)))) volume)
    (h_bound : ∀ᵐ (ξ : Fin 2 → ℝ), ∀ w ∈ s,
      ‖c ξ * (Complex.exp (I * (z 0 * ↑(ξ 0) + w * ↑(ξ 1))) * (I * ↑(ξ 1)))‖ ≤ bound ξ)
    (bound_int : Integrable bound volume) :
    HasDerivAt (fun w : ℂ => ∫ (ξ : Fin 2 → ℝ), c ξ * Complex.exp (I * (z 0 * ↑(ξ 0) + w * ↑(ξ 1))))
      (∫ (ξ : Fin 2 → ℝ),
        c ξ * (Complex.exp (I * (z 0 * ↑(ξ 0) + z 1 * ↑(ξ 1))) * (I * ↑(ξ 1)))) (z 1) := by
  have h_diff : ∀ᵐ (ξ : Fin 2 → ℝ), ∀ w ∈ s,
      HasDerivAt (fun w' => c ξ * Complex.exp (I * (z 0 * ↑(ξ 0) + w' * ↑(ξ 1))))
        (c ξ * (Complex.exp (I * (z 0 * ↑(ξ 0) + w * ↑(ξ 1))) * (I * ↑(ξ 1)))) w := by
    apply ae_of_all
    intro ξ w _hw
    exact fourier_integrand_deriv1 c ξ ![z 0, w]
  have h_res := hasDerivAt_integral_of_dominated_loc_of_deriv_le hs hF_meas hF_int hF'_meas
    h_bound bound_int h_diff
  exact h_res.2

lemma bochner_fourier_integral_holo_of_bound (c : (Fin 2 → ℝ) → ℂ) (U : Set (Fin 2 → ℂ))
    (h_dom : ∀ z ∈ U, ∃ (bound : (Fin 2 → ℝ) → ℝ), Integrable bound volume ∧ ∃ s ∈ 𝓝 z,
      (∀ᶠ w in 𝓝 z, AEStronglyMeasurable
        (fun ξ => c ξ * Complex.exp (I * (w 0 * ↑(ξ 0) + w 1 * ↑(ξ 1)))) volume) ∧
      Integrable (fun ξ => c ξ * Complex.exp (I * (z 0 * ↑(ξ 0) + z 1 * ↑(ξ 1)))) volume ∧
      AEStronglyMeasurable
        (fun ξ => fderiv ℂ
          (fun w => c ξ * Complex.exp (I * (w 0 * ↑(ξ 0) + w 1 * ↑(ξ 1)))) z) volume ∧
      (∀ᵐ ξ, ∀ w ∈ s,
        ‖fderiv ℂ
          (fun w' => c ξ * Complex.exp (I * (w' 0 * ↑(ξ 0) + w' 1 * ↑(ξ 1)))) w‖ ≤ bound ξ)) :
    DifferentiableOn ℂ
      (fun z : Fin 2 → ℂ =>
        ∫ (ξ : Fin 2 → ℝ), c ξ * Complex.exp (I * (z 0 * ↑(ξ 0) + z 1 * ↑(ξ 1)))) U := by
  have h_diff_integrand : ∀ (ξ : Fin 2 → ℝ) (w : Fin 2 → ℂ),
      HasFDerivAt (fun w' => c ξ * Complex.exp (I * (w' 0 * ↑(ξ 0) + w' 1 * ↑(ξ 1))))
        (fderiv ℂ (fun w' => c ξ * Complex.exp (I * (w' 0 * ↑(ξ 0) + w' 1 * ↑(ξ 1)))) w) w :=
    fun ξ w => (bochner_fourier_integrand_differentiable c ξ w).hasFDerivAt
  intro z hz
  rcases h_dom z hz with ⟨bound, bound_int, s, hs, hF_meas, hF_int, hF'_meas, h_le⟩
  have h_diff_s : ∀ᵐ ξ, ∀ w ∈ s,
      HasFDerivAt (fun w' => c ξ * Complex.exp (I * (w' 0 * ↑(ξ 0) + w' 1 * ↑(ξ 1))))
        (fderiv ℂ (fun w' => c ξ * Complex.exp (I * (w' 0 * ↑(ξ 0) + w' 1 * ↑(ξ 1)))) w) w :=
    ae_of_all _ (fun ξ w _hw => h_diff_integrand ξ w)
  have h_res := hasFDerivAt_integral_of_dominated_of_fderiv_le hs hF_meas hF_int hF'_meas
    h_le bound_int h_diff_s
  exact h_res.differentiableAt.differentiableWithinAt

lemma continuous_exp_fourier_kernel (x : Fin 2 → ℝ) :
    Continuous (fun (ξ : Fin 2 → ℝ) => Complex.exp (-I * (↑(x 0) * ↑(ξ 0) + ↑(x 1) * ↑(ξ 1)))) := by
  apply Complex.continuous_exp.comp
  apply continuous_const.mul
  apply Continuous.add
  · exact continuous_const.mul (Complex.continuous_ofReal.comp (continuous_apply 0))
  · exact continuous_const.mul (Complex.continuous_ofReal.comp (continuous_apply 1))

lemma continuous_exp_fourier_kernel_x (ξ : Fin 2 → ℝ) :
    Continuous (fun (x : Fin 2 → ℝ) => Complex.exp (-I * (↑(x 0) * ↑(ξ 0) + ↑(x 1) * ↑(ξ 1)))) := by
  apply Complex.continuous_exp.comp
  apply continuous_const.mul
  apply Continuous.add
  · exact (Complex.continuous_ofReal.comp (continuous_apply 0)).mul continuous_const
  · exact (Complex.continuous_ofReal.comp (continuous_apply 1)).mul continuous_const

lemma norm_exp_fourier_kernel_le_one (x ξ : Fin 2 → ℝ) :
    ‖Complex.exp (-I * (↑(x 0) * ↑(ξ 0) + ↑(x 1) * ↑(ξ 1)))‖ ≤ 1 := by
  have h_re : (-I * (↑(x 0) * ↑(ξ 0) + ↑(x 1) * ↑(ξ 1))).re = 0 := by simp
  rw [Complex.norm_exp, h_re, Real.exp_zero]

lemma continuous_bochner_fourier_transform_eps (f : (Fin 2 → ℂ) → ℂ) (ε : ℝ) (y : Fin 2 → ℝ)
    (hint : Integrable
      (fun x : Fin 2 → ℝ => bochner_f_eps f ε (fun i => ↑(x i) + I * ↑(y i))) volume) :
    Continuous (fun (ξ : Fin 2 → ℝ) => bochner_fourier_transform_eps f ε y ξ) := by
  unfold bochner_fourier_transform_eps
  have h_bound : ∀ (ξ : Fin 2 → ℝ), ∀ᵐ (x : Fin 2 → ℝ),
      ‖bochner_f_eps f ε (fun i => ↑(x i) + I * ↑(y i)) *
        Complex.exp (-I * (↑(x 0) * ↑(ξ 0) + ↑(x 1) * ↑(ξ 1)))‖ ≤
      ‖bochner_f_eps f ε (fun i => ↑(x i) + I * ↑(y i))‖ := by
    intro ξ
    apply ae_of_all
    intro x
    rw [norm_mul]
    have h1 := norm_exp_fourier_kernel_le_one x ξ
    calc ‖bochner_f_eps f ε (fun i => ↑(x i) + I * ↑(y i))‖ *
        ‖Complex.exp (-I * (↑(x 0) * ↑(ξ 0) + ↑(x 1) * ↑(ξ 1)))‖
      _ ≤ ‖bochner_f_eps f ε (fun i => ↑(x i) + I * ↑(y i))‖ * 1 :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = ‖bochner_f_eps f ε (fun i => ↑(x i) + I * ↑(y i))‖ := mul_one _
  have h_cont : ∀ᵐ (x : Fin 2 → ℝ),
      Continuous (fun (ξ : Fin 2 → ℝ) =>
        bochner_f_eps f ε (fun i => ↑(x i) + I * ↑(y i)) *
        Complex.exp (-I * (↑(x 0) * ↑(ξ 0) + ↑(x 1) * ↑(ξ 1)))) := by
    apply ae_of_all
    intro x
    exact continuous_const.mul (continuous_exp_fourier_kernel x)
  have h_meas : ∀ (ξ : Fin 2 → ℝ), AEStronglyMeasurable
      (fun (x : Fin 2 → ℝ) =>
        bochner_f_eps f ε (fun i => ↑(x i) + I * ↑(y i)) *
        Complex.exp (-I * (↑(x 0) * ↑(ξ 0) + ↑(x 1) * ↑(ξ 1)))) volume := by
    intro ξ
    apply AEStronglyMeasurable.mul hint.aestronglyMeasurable
    apply Continuous.aestronglyMeasurable
    exact continuous_exp_fourier_kernel_x ξ
  exact continuous_of_dominated h_meas h_bound hint.norm h_cont

lemma continuous_fourier_exp_phase (w : Fin 2 → ℂ) :
    Continuous (fun (ξ : Fin 2 → ℝ) => Complex.exp (I * (w 0 * ↑(ξ 0) + w 1 * ↑(ξ 1)))) := by
  apply Complex.continuous_exp.comp
  apply continuous_const.mul
  apply Continuous.add
  · exact continuous_const.mul (Complex.continuous_ofReal.comp (continuous_apply 0))
  · exact continuous_const.mul (Complex.continuous_ofReal.comp (continuous_apply 1))

lemma continuous_real_exp_phase (r : ℝ) :
    Continuous (fun (ξ : Fin 2 → ℝ) => Real.exp ((r/2) * ξ 0 + (r/2) * ξ 1)) := by
  apply Real.continuous_exp.comp
  apply Continuous.add
  · exact continuous_const.mul (continuous_apply 0)
  · exact continuous_const.mul (continuous_apply 1)

lemma bochner_f_eps_eq_bochner_integrand_F_zero (f : (Fin 2 → ℂ) → ℂ) (ε : ℝ) (z : Fin 2 → ℂ) :
    bochner_f_eps f ε z = bochner_integrand_F f ε 0 z := by
  unfold bochner_integrand_F
  simp

lemma continuous_bochner_c_eps (r R : ℝ) (_hr : 0 < r) (_hR : r < R)
    (f : (Fin 2 → ℂ) → ℂ) (hf_holo : DifferentiableOn ℂ f (TubeDomain (LShape r R)))
    (hf_bound : ∃ M : ℝ, ∀ z : Fin 2 → ℂ, ‖f z‖ ≤ M)
    (ε : ℝ) (hε : 0 < ε) :
    Continuous (fun (ξ : Fin 2 → ℝ) =>
      bochner_fourier_transform_eps f ε (fun _ => r/2) ξ *
        Real.exp ((r/2) * ξ 0 + (r/2) * ξ 1)) := by
  have hy0 : (fun _ : Fin 2 => r / 2) ∈ LShape r R := by
    unfold LShape
    left
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hint0 := bochner_integrand_integrable_2d r R f hf_holo hf_bound ε hε 0 (fun _ => r/2) hy0
  have heq : (fun x : Fin 2 → ℝ =>
        bochner_f_eps f ε (fun i => ↑(x i) + I * ↑((fun _ : Fin 2 => r/2) i))) =
      (fun x : Fin 2 → ℝ =>
        bochner_integrand_F f ε 0 (fun i => ↑(x i) + I * ↑((fun _ : Fin 2 => r/2) i))) := by
    ext x
    exact bochner_f_eps_eq_bochner_integrand_F_zero f ε
      (fun i => ↑(x i) + I * ↑((fun _ : Fin 2 => r/2) i))
  have hint : Integrable
      (fun x : Fin 2 → ℝ =>
        bochner_f_eps f ε (fun i => ↑(x i) + I * ↑((fun _ : Fin 2 => r/2) i))) volume := by
    rw [heq]
    exact hint0
  have h_cont_ft := continuous_bochner_fourier_transform_eps f ε (fun _ => r/2) hint
  apply Continuous.mul h_cont_ft
  exact Complex.continuous_ofReal.comp (continuous_real_exp_phase r)

lemma bochner_F_eps_integrand_aestronglyMeasurable (r R : ℝ) (hr : 0 < r) (hR : r < R)
    (f : (Fin 2 → ℂ) → ℂ) (hf_holo : DifferentiableOn ℂ f (TubeDomain (LShape r R)))
    (hf_bound : ∃ M : ℝ, ∀ z : Fin 2 → ℂ, ‖f z‖ ≤ M)
    (ε : ℝ) (hε : 0 < ε) (w : Fin 2 → ℂ) :
    AEStronglyMeasurable (fun ξ =>
      (bochner_fourier_transform_eps f ε (fun _ => r/2) ξ * Real.exp ((r/2) * ξ 0 + (r/2) * ξ 1)) *
      Complex.exp (I * (w 0 * ↑(ξ 0) + w 1 * ↑(ξ 1)))) volume := by
  have h_c_cont := continuous_bochner_c_eps r R hr hR f hf_holo hf_bound ε hε
  apply Continuous.aestronglyMeasurable
  exact h_c_cont.mul (continuous_fourier_exp_phase w)

noncomputable def fourier_proj (i : Fin 2) : (Fin 2 → ℂ) →L[ℂ] ℂ :=
  ContinuousLinearMap.proj (R := ℂ) (ι := Fin 2) (φ := fun _ => ℂ) i

lemma smulRight_eq_smul (i : Fin 2) (c : ℂ) :
    (fourier_proj i).smulRight c = c • fourier_proj i := by
  ext v
  simp only [fourier_proj, ContinuousLinearMap.smulRight_apply, smul_apply, proj_apply, smul_eq_mul]
  exact mul_comm _ _

lemma continuous_smulRight_fourier_proj (i : Fin 2) :
    Continuous (fun ξ : Fin 2 → ℝ => (fourier_proj i).smulRight (ξ i : ℂ)) := by
  have heq : (fun ξ : Fin 2 → ℝ => (fourier_proj i).smulRight (ξ i : ℂ)) =
      (fun ξ : Fin 2 → ℝ => (ξ i : ℂ) • fourier_proj i) := by
    funext ξ
    exact smulRight_eq_smul i (ξ i : ℂ)
  rw [heq]
  exact (Complex.continuous_ofReal.comp (continuous_apply i)).smul continuous_const

noncomputable def fourier_integrand_fderiv_clm
    (c : (Fin 2 → ℝ) → ℂ) (ξ : Fin 2 → ℝ) (z : Fin 2 → ℂ) :
    (Fin 2 → ℂ) →L[ℂ] ℂ :=
  (c ξ * Complex.exp (I * (z 0 * ↑(ξ 0) + z 1 * ↑(ξ 1))) * I) •
    ((fourier_proj 0).smulRight (ξ 0 : ℂ) + (fourier_proj 1).smulRight (ξ 1 : ℂ))

lemma continuous_fourier_integrand_fderiv_clm
    (c : (Fin 2 → ℝ) → ℂ) (hc : Continuous c) (z : Fin 2 → ℂ) :
    Continuous (fun ξ : Fin 2 → ℝ => fourier_integrand_fderiv_clm c ξ z) := by
  unfold fourier_integrand_fderiv_clm
  have h1 : Continuous
      (fun ξ : Fin 2 → ℝ => c ξ * Complex.exp (I * (z 0 * ↑(ξ 0) + z 1 * ↑(ξ 1))) * I) := by
    apply Continuous.mul
    · apply Continuous.mul hc
      apply Complex.continuous_exp.comp
      apply continuous_const.mul
      apply Continuous.add
      · exact continuous_const.mul (Complex.continuous_ofReal.comp (continuous_apply 0))
      · exact continuous_const.mul (Complex.continuous_ofReal.comp (continuous_apply 1))
    · exact continuous_const
  have h2 : Continuous (fun ξ : Fin 2 → ℝ =>
      (fourier_proj 0).smulRight (ξ 0 : ℂ) + (fourier_proj 1).smulRight (ξ 1 : ℂ)) :=
    (continuous_smulRight_fourier_proj 0).add (continuous_smulRight_fourier_proj 1)
  exact h1.smul h2

lemma hasFDerivAt_phase (ξ : Fin 2 → ℝ) (z : Fin 2 → ℂ) :
    HasFDerivAt (fun w : Fin 2 → ℂ => w 0 * ↑(ξ 0) + w 1 * ↑(ξ 1))
      ((fourier_proj 0).smulRight (ξ 0 : ℂ) + (fourier_proj 1).smulRight (ξ 1 : ℂ)) z := by
  have h0 : HasFDerivAt (fun w : Fin 2 → ℂ => w 0 * (ξ 0 : ℂ))
      ((fourier_proj 0).smulRight (ξ 0 : ℂ)) z := by
    have h := (fourier_proj 0).hasFDerivAt (x := z)
    exact h.smul_const (ξ 0 : ℂ)
  have h1 : HasFDerivAt (fun w : Fin 2 → ℂ => w 1 * (ξ 1 : ℂ))
      ((fourier_proj 1).smulRight (ξ 1 : ℂ)) z := by
    have h := (fourier_proj 1).hasFDerivAt (x := z)
    exact h.smul_const (ξ 1 : ℂ)
  exact h0.add h1

lemma fourier_integrand_hasFDerivAt (c : (Fin 2 → ℝ) → ℂ) (ξ : Fin 2 → ℝ) (z : Fin 2 → ℂ) :
    HasFDerivAt (fun w : Fin 2 → ℂ => c ξ * Complex.exp (I * (w 0 * ↑(ξ 0) + w 1 * ↑(ξ 1))))
      (fourier_integrand_fderiv_clm c ξ z) z := by
  have h_phase : HasFDerivAt (fun w : Fin 2 → ℂ => I * (w 0 * ↑(ξ 0) + w 1 * ↑(ξ 1)))
      (I • ((fourier_proj 0).smulRight (ξ 0 : ℂ) + (fourier_proj 1).smulRight (ξ 1 : ℂ))) z :=
    (hasFDerivAt_phase ξ z).const_mul I
  have h_exp := h_phase.cexp
  have h_mul := h_exp.const_mul (c ξ)
  unfold fourier_integrand_fderiv_clm
  have heq : c ξ • (Complex.exp (I * (z 0 * ↑(ξ 0) + z 1 * ↑(ξ 1))) •
      (I • ((fourier_proj 0).smulRight (ξ 0 : ℂ) + (fourier_proj 1).smulRight (ξ 1 : ℂ)))) =
      (c ξ * Complex.exp (I * (z 0 * ↑(ξ 0) + z 1 * ↑(ξ 1))) * I) •
        ((fourier_proj 0).smulRight (ξ 0 : ℂ) + (fourier_proj 1).smulRight (ξ 1 : ℂ)) := by
    rw [smul_smul, smul_smul, mul_assoc]
  rw [heq] at h_mul
  exact h_mul

lemma fourier_integrand_fderiv_eq (c : (Fin 2 → ℝ) → ℂ) (ξ : Fin 2 → ℝ) (z : Fin 2 → ℂ) :
    fderiv ℂ (fun w : Fin 2 → ℂ => c ξ * Complex.exp (I * (w 0 * ↑(ξ 0) + w 1 * ↑(ξ 1)))) z =
      fourier_integrand_fderiv_clm c ξ z :=
  (fourier_integrand_hasFDerivAt c ξ z).fderiv

lemma bochner_F_eps_integrand_fderiv_aestronglyMeasurable (r R : ℝ) (hr : 0 < r) (hR : r < R)
    (f : (Fin 2 → ℂ) → ℂ) (hf_holo : DifferentiableOn ℂ f (TubeDomain (LShape r R)))
    (hf_bound : ∃ M : ℝ, ∀ z : Fin 2 → ℂ, ‖f z‖ ≤ M)
    (ε : ℝ) (hε : 0 < ε) (z : Fin 2 → ℂ) :
    AEStronglyMeasurable (fun ξ => fderiv ℂ (fun (w : Fin 2 → ℂ) =>
      (bochner_fourier_transform_eps f ε (fun _ => r/2) ξ * Real.exp ((r/2) * ξ 0 + (r/2) * ξ 1)) *
      Complex.exp (I * (w 0 * ↑(ξ 0) + w 1 * ↑(ξ 1)))) z) volume := by
  let c : (Fin 2 → ℝ) → ℂ := fun ξ =>
    bochner_fourier_transform_eps f ε (fun _ => r/2) ξ * Real.exp ((r/2) * ξ 0 + (r/2) * ξ 1)
  have hc : Continuous c := continuous_bochner_c_eps r R hr hR f hf_holo hf_bound ε hε
  have heq : (fun ξ => fderiv ℂ (fun (w : Fin 2 → ℂ) =>
      c ξ * Complex.exp (I * (w 0 * ↑(ξ 0) + w 1 * ↑(ξ 1)))) z) =
      (fun ξ => fourier_integrand_fderiv_clm c ξ z) := by
    funext ξ
    exact fourier_integrand_fderiv_eq c ξ z
  rw [heq]
  exact (continuous_fourier_integrand_fderiv_clm c hc z).aestronglyMeasurable

lemma norm_proj_fin2_le (i : Fin 2) :
    ‖ContinuousLinearMap.proj (R := ℂ) (ι := Fin 2) (φ := fun _ => ℂ) i‖ ≤ 1 := by
  refine opNorm_le_bound _ zero_le_one fun v => ?_
  simp only [proj_apply, one_mul]
  exact norm_le_pi_norm v i

lemma clm_fin2_norm_le (a b : ℂ) :
    ‖(fourier_proj 0).smulRight a + (fourier_proj 1).smulRight b‖ ≤ ‖a‖ + ‖b‖ := by
  rw [smulRight_eq_smul 0 a, smulRight_eq_smul 1 b]
  refine (ContinuousLinearMap.opNorm_add_le _ _).trans ?_
  have ha : ‖a • fourier_proj 0‖ ≤ ‖a‖ := by
    refine (ContinuousLinearMap.opNorm_smul_le _ _).trans ?_
    calc ‖a‖ * ‖fourier_proj 0‖
      _ ≤ ‖a‖ * 1 := mul_le_mul_of_nonneg_left (norm_proj_fin2_le 0) (norm_nonneg _)
      _ = ‖a‖ := mul_one _
  have hb : ‖b • fourier_proj 1‖ ≤ ‖b‖ := by
    refine (ContinuousLinearMap.opNorm_smul_le _ _).trans ?_
    calc ‖b‖ * ‖fourier_proj 1‖
      _ ≤ ‖b‖ * 1 := mul_le_mul_of_nonneg_left (norm_proj_fin2_le 1) (norm_nonneg _)
      _ = ‖b‖ := mul_one _
  linarith

lemma norm_fourier_integrand_fderiv_clm_le (c : (Fin 2 → ℝ) → ℂ) (ξ : Fin 2 → ℝ) (z : Fin 2 → ℂ) :
    ‖fourier_integrand_fderiv_clm c ξ z‖ ≤
      ‖c ξ‖ * Real.exp (- (z 0).im * ξ 0 - (z 1).im * ξ 1) * (|ξ 0| + |ξ 1|) := by
  unfold fourier_integrand_fderiv_clm
  have h_smul := ContinuousLinearMap.opNorm_smul_le
    (c ξ * Complex.exp (I * (z 0 * ↑(ξ 0) + z 1 * ↑(ξ 1))) * I)
    ((fourier_proj 0).smulRight (ξ 0 : ℂ) + (fourier_proj 1).smulRight (ξ 1 : ℂ))
  have h_clm := clm_fin2_norm_le (ξ 0 : ℂ) (ξ 1 : ℂ)
  have h_I : ‖I‖ = 1 := norm_I
  have h_exp : ‖Complex.exp (I * (z 0 * ↑(ξ 0) + z 1 * ↑(ξ 1)))‖ =
      Real.exp (- (z 0).im * ξ 0 - (z 1).im * ξ 1) := by
    have h_re : (I * (z 0 * ↑(ξ 0) + z 1 * ↑(ξ 1))).re = - (z 0).im * ξ 0 - (z 1).im * ξ 1 := by
      simp
      ring
    rw [Complex.norm_exp, h_re]
  have h_scalar : ‖c ξ * Complex.exp (I * (z 0 * ↑(ξ 0) + z 1 * ↑(ξ 1))) * I‖ =
      ‖c ξ‖ * Real.exp (- (z 0).im * ξ 0 - (z 1).im * ξ 1) := by
    rw [norm_mul, norm_mul, h_I, mul_one, h_exp]
  rw [h_scalar] at h_smul
  have h_xi0 : ‖(ξ 0 : ℂ)‖ = |ξ 0| := Complex.norm_real (ξ 0)
  have h_xi1 : ‖(ξ 1 : ℂ)‖ = |ξ 1| := Complex.norm_real (ξ 1)
  rw [h_xi0, h_xi1] at h_clm
  refine h_smul.trans ?_
  exact mul_le_mul_of_nonneg_left h_clm (by positivity)

lemma closedBall_im_le (z : Fin 2 → ℂ) (w : Fin 2 → ℂ)
    (hw : w ∈ Metric.closedBall z 1) (i : Fin 2) :
    |(w i).im| ≤ |(z i).im| + 1 := by
  have h_dist : dist w z ≤ 1 := Metric.mem_closedBall.mp hw
  rw [dist_eq_norm] at h_dist
  have h_coord : ‖w i - z i‖ ≤ ‖w - z‖ := norm_le_pi_norm (w - z) i
  have h_le_one : ‖w i - z i‖ ≤ 1 := h_coord.trans h_dist
  have h_im_le : |(w i - z i).im| ≤ ‖w i - z i‖ := abs_im_le_norm (w i - z i)
  have h_diff_im : (w i - z i).im = (w i).im - (z i).im := by simp
  rw [h_diff_im] at h_im_le
  have h_sub_le : |(w i).im - (z i).im| ≤ 1 := h_im_le.trans h_le_one
  calc |(w i).im|
    _ = |(z i).im + ((w i).im - (z i).im)| := by ring_nf
    _ ≤ |(z i).im| + |(w i).im - (z i).im| := abs_add_le _ _
    _ ≤ |(z i).im| + 1 := by linarith

lemma exp_im_le (z : Fin 2 → ℂ) (w : Fin 2 → ℂ) (hw : w ∈ Metric.closedBall z 1) (ξ : Fin 2 → ℝ) :
    Real.exp (- (w 0).im * ξ 0 - (w 1).im * ξ 1) ≤
      Real.exp ((|(z 0).im| + 1) * |ξ 0| + (|(z 1).im| + 1) * |ξ 1|) := by
  apply Real.exp_le_exp.mpr
  have h0 : - (w 0).im * ξ 0 ≤ (|(z 0).im| + 1) * |ξ 0| := by
    have h_abs : - (w 0).im * ξ 0 ≤ |(w 0).im| * |ξ 0| := by
      calc - (w 0).im * ξ 0
        _ ≤ |- (w 0).im * ξ 0| := le_abs_self _
        _ = |(w 0).im| * |ξ 0| := by rw [abs_mul, abs_neg]
    have h_im := closedBall_im_le z w hw 0
    have h_le : |(w 0).im| * |ξ 0| ≤ (|(z 0).im| + 1) * |ξ 0| :=
      mul_le_mul_of_nonneg_right h_im (abs_nonneg _)
    exact h_abs.trans h_le
  have h1 : - (w 1).im * ξ 1 ≤ (|(z 1).im| + 1) * |ξ 1| := by
    have h_abs : - (w 1).im * ξ 1 ≤ |(w 1).im| * |ξ 1| := by
      calc - (w 1).im * ξ 1
        _ ≤ |- (w 1).im * ξ 1| := le_abs_self _
        _ = |(w 1).im| * |ξ 1| := by rw [abs_mul, abs_neg]
    have h_im := closedBall_im_le z w hw 1
    have h_le : |(w 1).im| * |ξ 1| ≤ (|(z 1).im| + 1) * |ξ 1| :=
      mul_le_mul_of_nonneg_right h_im (abs_nonneg _)
    exact h_abs.trans h_le
  linarith

lemma bochner_F_eps_integrand_norm_le_master (c : (Fin 2 → ℝ) → ℂ) (z : Fin 2 → ℂ) (ξ : Fin 2 → ℝ) :
    ‖(c ξ) * Complex.exp (I * (z 0 * ↑(ξ 0) + z 1 * ↑(ξ 1)))‖ ≤
      ‖c ξ‖ * Real.exp ((|(z 0).im| + 1) * |ξ 0| + (|(z 1).im| + 1) * |ξ 1|) *
        (|ξ 0| + |ξ 1| + 1) := by
  have h_exp : ‖Complex.exp (I * (z 0 * ↑(ξ 0) + z 1 * ↑(ξ 1)))‖ =
      Real.exp (- (z 0).im * ξ 0 - (z 1).im * ξ 1) := by
    have h_re : (I * (z 0 * ↑(ξ 0) + z 1 * ↑(ξ 1))).re = - (z 0).im * ξ 0 - (z 1).im * ξ 1 := by
      simp
      ring
    rw [Complex.norm_exp, h_re]
  have h_norm : ‖(c ξ) * Complex.exp (I * (z 0 * ↑(ξ 0) + z 1 * ↑(ξ 1)))‖ =
      ‖c ξ‖ * Real.exp (- (z 0).im * ξ 0 - (z 1).im * ξ 1) := by
    rw [norm_mul, h_exp]
  rw [h_norm]
  have h0 : - (z 0).im * ξ 0 ≤ |(z 0).im| * |ξ 0| := by
    calc - (z 0).im * ξ 0
      _ ≤ |- (z 0).im * ξ 0| := le_abs_self _
      _ = |(z 0).im| * |ξ 0| := by rw [abs_mul, abs_neg]
  have h0_le : |(z 0).im| * |ξ 0| ≤ (|(z 0).im| + 1) * |ξ 0| := by
    nlinarith [abs_nonneg (z 0).im, abs_nonneg (ξ 0)]
  have h0_trans : - (z 0).im * ξ 0 ≤ (|(z 0).im| + 1) * |ξ 0| := h0.trans h0_le
  have h1 : - (z 1).im * ξ 1 ≤ |(z 1).im| * |ξ 1| := by
    calc - (z 1).im * ξ 1
      _ ≤ |- (z 1).im * ξ 1| := le_abs_self _
      _ = |(z 1).im| * |ξ 1| := by rw [abs_mul, abs_neg]
  have h1_le : |(z 1).im| * |ξ 1| ≤ (|(z 1).im| + 1) * |ξ 1| := by
    nlinarith [abs_nonneg (z 1).im, abs_nonneg (ξ 1)]
  have h1_trans : - (z 1).im * ξ 1 ≤ (|(z 1).im| + 1) * |ξ 1| := h1.trans h1_le
  have h_sum :
      - (z 0).im * ξ 0 - (z 1).im * ξ 1 ≤
        (|(z 0).im| + 1) * |ξ 0| + (|(z 1).im| + 1) * |ξ 1| := by
    linarith
  have h_exp_le : Real.exp (- (z 0).im * ξ 0 - (z 1).im * ξ 1) ≤
      Real.exp ((|(z 0).im| + 1) * |ξ 0| + (|(z 1).im| + 1) * |ξ 1|) :=
    Real.exp_le_exp.mpr h_sum
  have h_mul_le : ‖c ξ‖ * Real.exp (- (z 0).im * ξ 0 - (z 1).im * ξ 1) ≤
      ‖c ξ‖ * Real.exp ((|(z 0).im| + 1) * |ξ 0| + (|(z 1).im| + 1) * |ξ 1|) :=
    mul_le_mul_of_nonneg_left h_exp_le (norm_nonneg _)
  have h_pos : 1 ≤ |ξ 0| + |ξ 1| + 1 := by
    have : 0 ≤ |ξ 0| + |ξ 1| := by positivity
    linarith
  calc ‖c ξ‖ * Real.exp (- (z 0).im * ξ 0 - (z 1).im * ξ 1)
    _ ≤ ‖c ξ‖ * Real.exp ((|(z 0).im| + 1) * |ξ 0| + (|(z 1).im| + 1) * |ξ 1|) * 1 := by
      rw [mul_one]
      exact h_mul_le
    _ ≤ ‖c ξ‖ * Real.exp ((|(z 0).im| + 1) * |ξ 0| + (|(z 1).im| + 1) * |ξ 1|) *
        (|ξ 0| + |ξ 1| + 1) := by
      refine mul_le_mul_of_nonneg_left h_pos ?_
      positivity

lemma bochner_F_eps_bound_le_master (c : (Fin 2 → ℝ) → ℂ) (z : Fin 2 → ℂ) (ξ : Fin 2 → ℝ) :
    ‖c ξ‖ * Real.exp ((|(z 0).im| + 1) * |ξ 0| + (|(z 1).im| + 1) * |ξ 1|) * (|ξ 0| + |ξ 1|) ≤
      ‖c ξ‖ * Real.exp ((|(z 0).im| + 1) * |ξ 0| + (|(z 1).im| + 1) * |ξ 1|) *
        (|ξ 0| + |ξ 1| + 1) := by
  have h_pos : |ξ 0| + |ξ 1| ≤ |ξ 0| + |ξ 1| + 1 := by linarith
  refine mul_le_mul_of_nonneg_left h_pos ?_
  positivity

lemma bochner_F_eps_bound_integrable_of_master (r R : ℝ) (hr : 0 < r) (hR : r < R)
    (f : (Fin 2 → ℂ) → ℂ) (hf_holo : DifferentiableOn ℂ f (TubeDomain (LShape r R)))
    (hf_bound : ∃ M : ℝ, ∀ z : Fin 2 → ℂ, ‖f z‖ ≤ M)
    (ε : ℝ) (hε : 0 < ε) (z : Fin 2 → ℂ)
    (h_master : Integrable (fun ξ =>
      ‖bochner_fourier_transform_eps f ε (fun _ => r/2) ξ * Real.exp ((r/2) * ξ 0 + (r/2) * ξ 1)‖ *
        Real.exp ((|(z 0).im| + 1) * |ξ 0| + (|(z 1).im| + 1) * |ξ 1|) *
        (|ξ 0| + |ξ 1| + 1)) volume) :
    Integrable (fun ξ =>
      (bochner_fourier_transform_eps f ε (fun _ => r/2) ξ * Real.exp ((r/2) * ξ 0 + (r/2) * ξ 1)) *
      Complex.exp (I * (z 0 * ↑(ξ 0) + z 1 * ↑(ξ 1)))) volume ∧
    Integrable (fun ξ =>
      ‖(bochner_fourier_transform_eps f ε (fun _ => r/2) ξ *
        Real.exp ((r/2) * ξ 0 + (r/2) * ξ 1))‖ *
        Real.exp ((|(z 0).im| + 1) * |ξ 0| + (|(z 1).im| + 1) * |ξ 1|) *
        (|ξ 0| + |ξ 1|)) volume := by
  let c : (Fin 2 → ℝ) → ℂ := fun ξ =>
    bochner_fourier_transform_eps f ε (fun _ => r/2) ξ * Real.exp ((r/2) * ξ 0 + (r/2) * ξ 1)
  have h_meas1 := bochner_F_eps_integrand_aestronglyMeasurable r R hr hR f hf_holo hf_bound ε hε z
  have h_le1 : ∀ᵐ ξ, ‖c ξ * Complex.exp (I * (z 0 * ↑(ξ 0) + z 1 * ↑(ξ 1)))‖ ≤
      ‖c ξ‖ * Real.exp ((|(z 0).im| + 1) * |ξ 0| + (|(z 1).im| + 1) * |ξ 1|) *
        (|ξ 0| + |ξ 1| + 1) := by
    apply ae_of_all
    intro ξ
    exact bochner_F_eps_integrand_norm_le_master c z ξ
  have hint1 : Integrable (fun ξ => c ξ * Complex.exp (I * (z 0 * ↑(ξ 0) + z 1 * ↑(ξ 1)))) volume :=
    Integrable.mono' h_master h_meas1 h_le1
  have h_cont_c : Continuous c :=
    continuous_bochner_c_eps r R hr hR f hf_holo hf_bound ε hε
  have h_cont_bound : Continuous (fun ξ =>
      ‖c ξ‖ * Real.exp ((|(z 0).im| + 1) * |ξ 0| + (|(z 1).im| + 1) * |ξ 1|) *
        (|ξ 0| + |ξ 1|)) := by
    apply Continuous.mul
    · apply Continuous.mul h_cont_c.norm
      apply Real.continuous_exp.comp
      apply Continuous.add
      · exact continuous_const.mul (continuous_apply 0).abs
      · exact continuous_const.mul (continuous_apply 1).abs
    · apply Continuous.add
      · exact (continuous_apply 0).abs
      · exact (continuous_apply 1).abs
  have h_meas2 : AEStronglyMeasurable (fun ξ =>
      ‖c ξ‖ * Real.exp ((|(z 0).im| + 1) * |ξ 0| + (|(z 1).im| + 1) * |ξ 1|) *
        (|ξ 0| + |ξ 1|)) volume :=
    h_cont_bound.aestronglyMeasurable
  have h_le2 : ∀ᵐ ξ,
      ‖‖c ξ‖ * Real.exp ((|(z 0).im| + 1) * |ξ 0| + (|(z 1).im| + 1) * |ξ 1|) *
        (|ξ 0| + |ξ 1|)‖ ≤
        ‖c ξ‖ * Real.exp ((|(z 0).im| + 1) * |ξ 0| + (|(z 1).im| + 1) * |ξ 1|) *
          (|ξ 0| + |ξ 1| + 1) := by
    apply ae_of_all
    intro ξ
    have h_nonneg : 0 ≤
        ‖c ξ‖ * Real.exp ((|(z 0).im| + 1) * |ξ 0| + (|(z 1).im| + 1) * |ξ 1|) *
          (|ξ 0| + |ξ 1|) := by
      positivity
    rw [Real.norm_of_nonneg h_nonneg]
    exact bochner_F_eps_bound_le_master c z ξ
  have hint2 : Integrable (fun ξ =>
      ‖c ξ‖ * Real.exp ((|(z 0).im| + 1) * |ξ 0| + (|(z 1).im| + 1) * |ξ 1|) *
        (|ξ 0| + |ξ 1|)) volume :=
    Integrable.mono' h_master h_meas2 h_le2
  exact ⟨hint1, hint2⟩

lemma poly_le_exp_add (x y : ℝ) :
    |x| + |y| + 1 ≤ Real.exp (|x| + |y|) := by
  have h_add : |x| + |y| + 1 ≤ (|x| + 1) * (|y| + 1) := by
    nlinarith [abs_nonneg x, abs_nonneg y]
  have h_exp_x : |x| + 1 ≤ Real.exp |x| := Real.add_one_le_exp |x|
  have h_exp_y : |y| + 1 ≤ Real.exp |y| := Real.add_one_le_exp |y|
  have h_mul_exp : (|x| + 1) * (|y| + 1) ≤ Real.exp |x| * Real.exp |y| :=
    mul_le_mul h_exp_x h_exp_y (by positivity) (Real.exp_pos _).le
  rw [← Real.exp_add] at h_mul_exp
  exact h_add.trans h_mul_exp

lemma exp_neg_sq_add_mul_le (α K x : ℝ) (hα : 0 < α) :
    - α * x ^ 2 + K * |x| ≤ - (α / 2) * x ^ 2 + K ^ 2 / (2 * α) := by
  have h_sq : 0 ≤ (Real.sqrt (α / 2) * |x| - K / (2 * Real.sqrt (α / 2))) ^ 2 := sq_nonneg _
  have h_pos : 0 < α / 2 := by linarith
  have h_sqrt_pos : 0 < Real.sqrt (α / 2) := Real.sqrt_pos.mpr h_pos
  have h_sqrt_sq : (Real.sqrt (α / 2)) ^ 2 = α / 2 := Real.sq_sqrt (by linarith)
  have h_expand : (Real.sqrt (α / 2) * |x| - K / (2 * Real.sqrt (α / 2))) ^ 2 =
      (α / 2) * x ^ 2 - K * |x| + K ^ 2 / (2 * α) := by
    calc (Real.sqrt (α / 2) * |x| - K / (2 * Real.sqrt (α / 2))) ^ 2
      _ = (Real.sqrt (α / 2) * |x|) ^ 2 -
          2 * (Real.sqrt (α / 2) * |x|) * (K / (2 * Real.sqrt (α / 2))) +
          (K / (2 * Real.sqrt (α / 2))) ^ 2 := by ring
      _ = (Real.sqrt (α / 2)) ^ 2 * (|x|) ^ 2 -
          (2 * (K / 2)) * ((Real.sqrt (α / 2) / Real.sqrt (α / 2)) * |x|) +
          K ^ 2 / (4 * (Real.sqrt (α / 2)) ^ 2) := by ring
      _ = (α / 2) * x ^ 2 - K * |x| + K ^ 2 / (2 * α) := by
        rw [h_sqrt_sq, sq_abs]
        have h_div : Real.sqrt (α / 2) / Real.sqrt (α / 2) = 1 := div_self (ne_of_gt h_sqrt_pos)
        rw [h_div]
        ring
  rw [h_expand] at h_sq
  linarith

lemma gaussian_mul_exp_poly_le (α K₀ K₁ : ℝ) (hα : 0 < α) (ξ : Fin 2 → ℝ) :
    Real.exp (- α * (ξ 0 ^ 2 + ξ 1 ^ 2)) *
      Real.exp (K₀ * |ξ 0| + K₁ * |ξ 1|) * (|ξ 0| + |ξ 1| + 1) ≤
      Real.exp ((K₀ + 1) ^ 2 / (2 * α) + (K₁ + 1) ^ 2 / (2 * α)) *
      Real.exp (- (α / 2) * (ξ 0 ^ 2 + ξ 1 ^ 2)) := by
  have h_poly := poly_le_exp_add (ξ 0) (ξ 1)
  have h1 : Real.exp (- α * (ξ 0 ^ 2 + ξ 1 ^ 2)) *
        Real.exp (K₀ * |ξ 0| + K₁ * |ξ 1|) * (|ξ 0| + |ξ 1| + 1) ≤
      Real.exp (- α * (ξ 0 ^ 2 + ξ 1 ^ 2)) *
        Real.exp (K₀ * |ξ 0| + K₁ * |ξ 1|) * Real.exp (|ξ 0| + |ξ 1|) :=
    mul_le_mul_of_nonneg_left h_poly (by positivity)
  have h_le0 := exp_neg_sq_add_mul_le α (K₀ + 1) (ξ 0) hα
  have h_le1 := exp_neg_sq_add_mul_le α (K₁ + 1) (ξ 1) hα
  have h_sum : (- α * ξ 0 ^ 2 + (K₀ + 1) * |ξ 0|) + (- α * ξ 1 ^ 2 + (K₁ + 1) * |ξ 1|) ≤
      ((K₀ + 1) ^ 2 / (2 * α) + (K₁ + 1) ^ 2 / (2 * α)) + (- (α / 2) * (ξ 0 ^ 2 + ξ 1 ^ 2)) := by
    linarith
  have h_exp_le :
      Real.exp ((- α * ξ 0 ^ 2 + (K₀ + 1) * |ξ 0|) + (- α * ξ 1 ^ 2 + (K₁ + 1) * |ξ 1|)) ≤
        Real.exp (((K₀ + 1) ^ 2 / (2 * α) + (K₁ + 1) ^ 2 / (2 * α)) +
          (- (α / 2) * (ξ 0 ^ 2 + ξ 1 ^ 2))) :=
    Real.exp_le_exp.mpr h_sum
  have h_exp_left :
      Real.exp (- α * (ξ 0 ^ 2 + ξ 1 ^ 2)) * Real.exp (K₀ * |ξ 0| + K₁ * |ξ 1|) *
        Real.exp (|ξ 0| + |ξ 1|) =
      Real.exp ((- α * ξ 0 ^ 2 + (K₀ + 1) * |ξ 0|) + (- α * ξ 1 ^ 2 + (K₁ + 1) * |ξ 1|)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have h_exp_right :
      Real.exp (((K₀ + 1) ^ 2 / (2 * α) + (K₁ + 1) ^ 2 / (2 * α)) +
        (- (α / 2) * (ξ 0 ^ 2 + ξ 1 ^ 2))) =
      Real.exp ((K₀ + 1) ^ 2 / (2 * α) + (K₁ + 1) ^ 2 / (2 * α)) *
        Real.exp (- (α / 2) * (ξ 0 ^ 2 + ξ 1 ^ 2)) := by
    rw [Real.exp_add]
  calc Real.exp (- α * (ξ 0 ^ 2 + ξ 1 ^ 2)) * Real.exp (K₀ * |ξ 0| + K₁ * |ξ 1|) *
        (|ξ 0| + |ξ 1| + 1)
    _ ≤ Real.exp (- α * (ξ 0 ^ 2 + ξ 1 ^ 2)) * Real.exp (K₀ * |ξ 0| + K₁ * |ξ 1|) *
        Real.exp (|ξ 0| + |ξ 1|) := h1
    _ = Real.exp ((- α * ξ 0 ^ 2 + (K₀ + 1) * |ξ 0|) +
        (- α * ξ 1 ^ 2 + (K₁ + 1) * |ξ 1|)) := h_exp_left
    _ ≤ Real.exp (((K₀ + 1) ^ 2 / (2 * α) + (K₁ + 1) ^ 2 / (2 * α)) +
        (- (α / 2) * (ξ 0 ^ 2 + ξ 1 ^ 2))) := h_exp_le
    _ = Real.exp ((K₀ + 1) ^ 2 / (2 * α) + (K₁ + 1) ^ 2 / (2 * α)) *
        Real.exp (- (α / 2) * (ξ 0 ^ 2 + ξ 1 ^ 2)) := h_exp_right

lemma integrable_gaussian_mul_exp_poly (C α K₀ K₁ : ℝ) (hC : 0 ≤ C) (hα : 0 < α) :
    Integrable (fun ξ : Fin 2 → ℝ =>
      C * Real.exp (- α * (ξ 0 ^ 2 + ξ 1 ^ 2)) *
        Real.exp (K₀ * |ξ 0| + K₁ * |ξ 1|) * (|ξ 0| + |ξ 1| + 1)) volume := by
  have h_pos : 0 < α / 2 := by linarith
  have hint_gauss :
      Integrable (fun ξ : Fin 2 → ℝ => Real.exp (- (α / 2) * (ξ 0 ^ 2 + ξ 1 ^ 2))) volume :=
    integrable_gaussian_2d (α / 2) h_pos
  let C' := C * Real.exp ((K₀ + 1) ^ 2 / (2 * α) + (K₁ + 1) ^ 2 / (2 * α))
  have hint_bound :
      Integrable (fun ξ : Fin 2 → ℝ => C' * Real.exp (- (α / 2) * (ξ 0 ^ 2 + ξ 1 ^ 2))) volume :=
    hint_gauss.const_mul C'
  have h_cont : Continuous (fun ξ : Fin 2 → ℝ =>
      C * Real.exp (- α * (ξ 0 ^ 2 + ξ 1 ^ 2)) *
        Real.exp (K₀ * |ξ 0| + K₁ * |ξ 1|) * (|ξ 0| + |ξ 1| + 1)) := by
    apply Continuous.mul
    · apply Continuous.mul
      · apply continuous_const.mul
        apply Real.continuous_exp.comp
        apply continuous_const.mul
        apply Continuous.add
        · exact (continuous_apply 0).pow 2
        · exact (continuous_apply 1).pow 2
      · apply Real.continuous_exp.comp
        apply Continuous.add
        · exact continuous_const.mul (continuous_apply 0).abs
        · exact continuous_const.mul (continuous_apply 1).abs
    · apply Continuous.add
      · apply Continuous.add
        · exact (continuous_apply 0).abs
        · exact (continuous_apply 1).abs
      · exact continuous_const
  have h_meas : AEStronglyMeasurable (fun ξ : Fin 2 → ℝ =>
      C * Real.exp (- α * (ξ 0 ^ 2 + ξ 1 ^ 2)) *
        Real.exp (K₀ * |ξ 0| + K₁ * |ξ 1|) * (|ξ 0| + |ξ 1| + 1)) volume :=
    h_cont.aestronglyMeasurable
  have h_le : ∀ᵐ ξ : Fin 2 → ℝ,
      ‖C * Real.exp (- α * (ξ 0 ^ 2 + ξ 1 ^ 2)) *
        Real.exp (K₀ * |ξ 0| + K₁ * |ξ 1|) * (|ξ 0| + |ξ 1| + 1)‖ ≤
        C' * Real.exp (- (α / 2) * (ξ 0 ^ 2 + ξ 1 ^ 2)) := by
    apply ae_of_all
    intro ξ
    have h_nonneg : 0 ≤ C * Real.exp (- α * (ξ 0 ^ 2 + ξ 1 ^ 2)) *
        Real.exp (K₀ * |ξ 0| + K₁ * |ξ 1|) * (|ξ 0| + |ξ 1| + 1) := by
      positivity
    rw [Real.norm_of_nonneg h_nonneg]
    have h_ineq := gaussian_mul_exp_poly_le α K₀ K₁ hα ξ
    dsimp [C']
    calc C * Real.exp (- α * (ξ 0 ^ 2 + ξ 1 ^ 2)) *
          Real.exp (K₀ * |ξ 0| + K₁ * |ξ 1|) * (|ξ 0| + |ξ 1| + 1)
      _ = C * (Real.exp (- α * (ξ 0 ^ 2 + ξ 1 ^ 2)) *
          Real.exp (K₀ * |ξ 0| + K₁ * |ξ 1|) * (|ξ 0| + |ξ 1| + 1)) := by ring
      _ ≤ C * (Real.exp ((K₀ + 1) ^ 2 / (2 * α) + (K₁ + 1) ^ 2 / (2 * α)) *
          Real.exp (- (α / 2) * (ξ 0 ^ 2 + ξ 1 ^ 2))) :=
        mul_le_mul_of_nonneg_left h_ineq hC
      _ = C * Real.exp ((K₀ + 1) ^ 2 / (2 * α) + (K₁ + 1) ^ 2 / (2 * α)) *
          Real.exp (- (α / 2) * (ξ 0 ^ 2 + ξ 1 ^ 2)) := by ring
  exact Integrable.mono' hint_bound h_meas h_le

lemma bochner_F_eps_integrable_master_of_decay (r R : ℝ) (hr : 0 < r) (hR : r < R)
    (f : (Fin 2 → ℂ) → ℂ) (hf_holo : DifferentiableOn ℂ f (TubeDomain (LShape r R)))
    (hf_bound : ∃ M : ℝ, ∀ z : Fin 2 → ℂ, ‖f z‖ ≤ M)
    (ε : ℝ) (hε : 0 < ε) (z : Fin 2 → ℂ)
    (h_decay : ∃ C α : ℝ, 0 ≤ C ∧ 0 < α ∧ ∀ ξ : Fin 2 → ℝ,
      ‖bochner_fourier_transform_eps f ε (fun _ => r/2) ξ * Real.exp ((r/2) * ξ 0 + (r/2) * ξ 1)‖ ≤
        C * Real.exp (- α * (ξ 0 ^ 2 + ξ 1 ^ 2))) :
    Integrable (fun ξ =>
      ‖bochner_fourier_transform_eps f ε (fun _ => r/2) ξ * Real.exp ((r/2) * ξ 0 + (r/2) * ξ 1)‖ *
        Real.exp ((|(z 0).im| + 1) * |ξ 0| + (|(z 1).im| + 1) * |ξ 1|) *
        (|ξ 0| + |ξ 1| + 1)) volume := by
  rcases h_decay with ⟨C, α, hC, hα, h_decay_le⟩
  let K₀ := |(z 0).im| + 1
  let K₁ := |(z 1).im| + 1
  have hint_bound := integrable_gaussian_mul_exp_poly C α K₀ K₁ hC hα
  have h_cont_c : Continuous (fun ξ =>
      bochner_fourier_transform_eps f ε (fun _ => r/2) ξ * Real.exp ((r/2) * ξ 0 + (r/2) * ξ 1)) :=
    continuous_bochner_c_eps r R hr hR f hf_holo hf_bound ε hε
  have h_cont : Continuous (fun ξ =>
      ‖bochner_fourier_transform_eps f ε (fun _ => r/2) ξ * Real.exp ((r/2) * ξ 0 + (r/2) * ξ 1)‖ *
      Real.exp ((|(z 0).im| + 1) * |ξ 0| + (|(z 1).im| + 1) * |ξ 1|) * (|ξ 0| + |ξ 1| + 1)) := by
    apply Continuous.mul
    · apply Continuous.mul h_cont_c.norm
      apply Real.continuous_exp.comp
      apply Continuous.add
      · exact continuous_const.mul (continuous_apply 0).abs
      · exact continuous_const.mul (continuous_apply 1).abs
    · apply Continuous.add
      · apply Continuous.add
        · exact (continuous_apply 0).abs
        · exact (continuous_apply 1).abs
      · exact continuous_const
  have h_meas : AEStronglyMeasurable (fun ξ =>
      ‖bochner_fourier_transform_eps f ε (fun _ => r/2) ξ * Real.exp ((r/2) * ξ 0 + (r/2) * ξ 1)‖ *
        Real.exp ((|(z 0).im| + 1) * |ξ 0| + (|(z 1).im| + 1) * |ξ 1|) *
        (|ξ 0| + |ξ 1| + 1)) volume :=
    h_cont.aestronglyMeasurable
  have h_le : ∀ᵐ ξ : Fin 2 → ℝ,
      ‖‖bochner_fourier_transform_eps f ε (fun _ => r/2) ξ *
          Real.exp ((r/2) * ξ 0 + (r/2) * ξ 1)‖ *
        Real.exp ((|(z 0).im| + 1) * |ξ 0| + (|(z 1).im| + 1) * |ξ 1|) *
        (|ξ 0| + |ξ 1| + 1)‖ ≤
        C * Real.exp (- α * (ξ 0 ^ 2 + ξ 1 ^ 2)) *
          Real.exp (K₀ * |ξ 0| + K₁ * |ξ 1|) * (|ξ 0| + |ξ 1| + 1) := by
    apply ae_of_all
    intro ξ
    have h_nonneg : 0 ≤
        ‖bochner_fourier_transform_eps f ε (fun _ => r/2) ξ *
          Real.exp ((r/2) * ξ 0 + (r/2) * ξ 1)‖ *
          Real.exp ((|(z 0).im| + 1) * |ξ 0| + (|(z 1).im| + 1) * |ξ 1|) *
          (|ξ 0| + |ξ 1| + 1) := by
      positivity
    rw [Real.norm_of_nonneg h_nonneg]
    have h_dec := h_decay_le ξ
    have h_exp_nonneg : 0 ≤ Real.exp ((|(z 0).im| + 1) * |ξ 0| + (|(z 1).im| + 1) * |ξ 1|) *
        (|ξ 0| + |ξ 1| + 1) := by
      positivity
    dsimp [K₀, K₁]
    calc ‖bochner_fourier_transform_eps f ε (fun _ => r/2) ξ *
          Real.exp ((r/2) * ξ 0 + (r/2) * ξ 1)‖ *
          Real.exp ((|(z 0).im| + 1) * |ξ 0| + (|(z 1).im| + 1) * |ξ 1|) *
          (|ξ 0| + |ξ 1| + 1)
      _ = (‖bochner_fourier_transform_eps f ε (fun _ => r/2) ξ *
            Real.exp ((r/2) * ξ 0 + (r/2) * ξ 1)‖) *
          (Real.exp ((|(z 0).im| + 1) * |ξ 0| + (|(z 1).im| + 1) * |ξ 1|) *
            (|ξ 0| + |ξ 1| + 1)) := by ring
      _ ≤ (C * Real.exp (- α * (ξ 0 ^ 2 + ξ 1 ^ 2))) *
          (Real.exp ((|(z 0).im| + 1) * |ξ 0| + (|(z 1).im| + 1) * |ξ 1|) *
            (|ξ 0| + |ξ 1| + 1)) :=
        mul_le_mul_of_nonneg_right h_dec h_exp_nonneg
      _ = C * Real.exp (- α * (ξ 0 ^ 2 + ξ 1 ^ 2)) *
          Real.exp ((|(z 0).im| + 1) * |ξ 0| + (|(z 1).im| + 1) * |ξ 1|) *
          (|ξ 0| + |ξ 1| + 1) := by ring
  exact Integrable.mono' hint_bound h_meas h_le

lemma bochner_F_eps_integrand_bound_integrable (r R : ℝ) (hr : 0 < r) (hR : r < R)
    (f : (Fin 2 → ℂ) → ℂ) (hf_holo : DifferentiableOn ℂ f (TubeDomain (LShape r R)))
    (hf_bound : ∃ M : ℝ, ∀ z : Fin 2 → ℂ, ‖f z‖ ≤ M)
    (ε : ℝ) (hε : 0 < ε) (z : Fin 2 → ℂ) (hz : z ∈ TubeDomain (LShapeConvexHull r R)) :
    ∃ (bound : (Fin 2 → ℝ) → ℝ), Integrable bound volume ∧ ∃ s ∈ 𝓝 z,
      Integrable (fun ξ =>
        (bochner_fourier_transform_eps f ε (fun _ => r/2) ξ *
          Real.exp ((r/2) * ξ 0 + (r/2) * ξ 1)) *
        Complex.exp (I * (z 0 * ↑(ξ 0) + z 1 * ↑(ξ 1)))) volume ∧
      (∀ᵐ ξ, ∀ w ∈ s, ‖fderiv ℂ (fun (w' : Fin 2 → ℂ) =>
        (bochner_fourier_transform_eps f ε (fun _ => r/2) ξ *
          Real.exp ((r/2) * ξ 0 + (r/2) * ξ 1)) *
        Complex.exp (I * (w' 0 * ↑(ξ 0) + w' 1 * ↑(ξ 1)))) w‖ ≤ bound ξ) := by
  let c : (Fin 2 → ℝ) → ℂ := fun ξ =>
    bochner_fourier_transform_eps f ε (fun _ => r/2) ξ * Real.exp ((r/2) * ξ 0 + (r/2) * ξ 1)
  have hc_eq (ξ : Fin 2 → ℝ) :
      bochner_fourier_transform_eps f ε (fun _ => r/2) ξ *
        ↑(Real.exp ((r/2) * ξ 0 + (r/2) * ξ 1)) = c ξ := rfl
  let y' : Fin 2 → ℝ := fun i => (z i).im
  have hy' : y' ∈ LShapeConvexHull r R := hz
  rcases bochner_c_eps_local_exp_decay r R hr hR f hf_holo hf_bound ε hε y' hy' with
    ⟨C, δ, hC, hδ_pos, h_decay⟩
  let η := δ / 4
  have hη_pos : 0 < η := by positivity
  let s := Metric.closedBall z η
  have hs : s ∈ 𝓝 z := Metric.closedBall_mem_nhds z hη_pos
  let bound : (Fin 2 → ℝ) → ℝ := fun ξ =>
    C * (Real.exp (-(δ / 2) * (|ξ 0| + |ξ 1|)) * (|ξ 0| + |ξ 1| + 1))
  have hδ2_pos : 0 < δ / 2 := by positivity
  have h_int_poly := integrable_exp_neg_abs_poly_2d (δ / 2) hδ2_pos
  have hbound_int : Integrable bound volume := h_int_poly.const_mul C
  have hint_z :
      Integrable (fun ξ => c ξ * Complex.exp (I * (z 0 * ↑(ξ 0) + z 1 * ↑(ξ 1)))) volume := by
    have h_cont_c := continuous_bochner_c_eps r R hr hR f hf_holo hf_bound ε hε
    have h_cont : Continuous (fun ξ => c ξ * Complex.exp (I * (z 0 * ↑(ξ 0) + z 1 * ↑(ξ 1)))) := by
      apply Continuous.mul h_cont_c
      apply Complex.continuous_exp.comp
      apply continuous_const.mul
      apply Continuous.add
      · exact continuous_const.mul (continuous_ofReal.comp (continuous_apply 0))
      · exact continuous_const.mul (continuous_ofReal.comp (continuous_apply 1))
    have h_meas : AEStronglyMeasurable
        (fun ξ => c ξ * Complex.exp (I * (z 0 * ↑(ξ 0) + z 1 * ↑(ξ 1)))) volume :=
      h_cont.aestronglyMeasurable
    have h_le : ∀ᵐ ξ, ‖c ξ * Complex.exp (I * (z 0 * ↑(ξ 0) + z 1 * ↑(ξ 1)))‖ ≤ bound ξ := by
      apply ae_of_all
      intro ξ
      rw [norm_mul]
      have h_norm_exp : ‖Complex.exp (I * (z 0 * ↑(ξ 0) + z 1 * ↑(ξ 1)))‖ =
          Real.exp (-(y' 0 * ξ 0 + y' 1 * ξ 1)) := by
        have h_re : (I * (z 0 * ↑(ξ 0) + z 1 * ↑(ξ 1))).re = - (z 0).im * ξ 0 - (z 1).im * ξ 1 := by
          simp
          ring
        rw [Complex.norm_exp, h_re]
        dsimp [y']
        congr 1
        ring
      rw [h_norm_exp]
      have h_dec := h_decay ξ
      rw [hc_eq] at h_dec
      calc ‖c ξ‖ * Real.exp (-(y' 0 * ξ 0 + y' 1 * ξ 1))
        _ ≤ C * Real.exp (-δ * (|ξ 0| + |ξ 1|)) := h_dec
        _ ≤ C * (Real.exp (-(δ / 2) * (|ξ 0| + |ξ 1|)) * (|ξ 0| + |ξ 1| + 1)) := by
          have h_exp_le :
              Real.exp (-δ * (|ξ 0| + |ξ 1|)) ≤ Real.exp (-(δ / 2) * (|ξ 0| + |ξ 1|)) := by
            refine Real.exp_le_exp.mpr ?_
            have : 0 ≤ |ξ 0| + |ξ 1| := by positivity
            nlinarith
          have h_one_le : 1 ≤ |ξ 0| + |ξ 1| + 1 := by
            have : 0 ≤ |ξ 0| + |ξ 1| := by positivity
            linarith
          have : Real.exp (-δ * (|ξ 0| + |ξ 1|)) ≤
              Real.exp (-(δ / 2) * (|ξ 0| + |ξ 1|)) * (|ξ 0| + |ξ 1| + 1) := by
            calc Real.exp (-δ * (|ξ 0| + |ξ 1|))
              _ = Real.exp (-δ * (|ξ 0| + |ξ 1|)) * 1 := (mul_one _).symm
              _ ≤ Real.exp (-(δ / 2) * (|ξ 0| + |ξ 1|)) * (|ξ 0| + |ξ 1| + 1) := by
                exact mul_le_mul h_exp_le h_one_le zero_le_one (by positivity)
          exact mul_le_mul_of_nonneg_left this hC
    exact Integrable.mono' hbound_int h_meas h_le
  refine ⟨bound, hbound_int, s, hs, hint_z, ?_⟩
  apply ae_of_all
  intro ξ w hw
  rw [fourier_integrand_fderiv_eq c ξ w]
  have h_norm := norm_fourier_integrand_fderiv_clm_le c ξ w
  have h_exp_im := exp_im_diff_le hw ξ
  calc ‖fourier_integrand_fderiv_clm c ξ w‖
    _ ≤ ‖c ξ‖ * Real.exp (- (w 0).im * ξ 0 - (w 1).im * ξ 1) * (|ξ 0| + |ξ 1|) := h_norm
    _ ≤ ‖c ξ‖ * (Real.exp (-(z 0).im * ξ 0 - (z 1).im * ξ 1 + η * (|ξ 0| + |ξ 1|))) *
        (|ξ 0| + |ξ 1|) := by
      gcongr
    _ = (‖c ξ‖ * Real.exp (-(y' 0 * ξ 0 + y' 1 * ξ 1))) *
        Real.exp (η * (|ξ 0| + |ξ 1|)) * (|ξ 0| + |ξ 1|) := by
      dsimp [y']
      rw [Real.exp_add]
      ring_nf
    _ ≤ (C * Real.exp (-δ * (|ξ 0| + |ξ 1|))) *
        Real.exp (η * (|ξ 0| + |ξ 1|)) * (|ξ 0| + |ξ 1|) := by
      have h_dec := h_decay ξ
      rw [hc_eq] at h_dec
      gcongr
    _ = C * (Real.exp (-δ * (|ξ 0| + |ξ 1|)) * Real.exp (η * (|ξ 0| + |ξ 1|))) *
        (|ξ 0| + |ξ 1|) := by ring
    _ = C * Real.exp (-δ * (|ξ 0| + |ξ 1|) + η * (|ξ 0| + |ξ 1|)) * (|ξ 0| + |ξ 1|) := by
      rw [← Real.exp_add]
    _ = C * Real.exp (-(δ - η) * (|ξ 0| + |ξ 1|)) * (|ξ 0| + |ξ 1|) := by
      congr 2
      ring_nf
    _ ≤ C * (Real.exp (-(δ / 2) * (|ξ 0| + |ξ 1|)) * (|ξ 0| + |ξ 1| + 1)) := by
      have h_exp_le :
          Real.exp (-(δ - η) * (|ξ 0| + |ξ 1|)) ≤ Real.exp (-(δ / 2) * (|ξ 0| + |ξ 1|)) := by
        refine Real.exp_le_exp.mpr ?_
        have : δ / 2 ≤ δ - η := by dsimp [η]; linarith
        have : 0 ≤ |ξ 0| + |ξ 1| := by positivity
        nlinarith
      have h_poly_le : |ξ 0| + |ξ 1| ≤ |ξ 0| + |ξ 1| + 1 := by linarith
      have : Real.exp (-(δ - η) * (|ξ 0| + |ξ 1|)) * (|ξ 0| + |ξ 1|) ≤
          Real.exp (-(δ / 2) * (|ξ 0| + |ξ 1|)) * (|ξ 0| + |ξ 1| + 1) := by
        exact mul_le_mul h_exp_le h_poly_le (by positivity) (by positivity)
      calc C * Real.exp (-(δ - η) * (|ξ 0| + |ξ 1|)) * (|ξ 0| + |ξ 1|)
        _ = C * (Real.exp (-(δ - η) * (|ξ 0| + |ξ 1|)) * (|ξ 0| + |ξ 1|)) := by ring
        _ ≤ C * (Real.exp (-(δ / 2) * (|ξ 0| + |ξ 1|)) * (|ξ 0| + |ξ 1| + 1)) :=
          mul_le_mul_of_nonneg_left this hC

lemma bochner_F_eps_integrand_dom (r R : ℝ) (hr : 0 < r) (hR : r < R)
    (f : (Fin 2 → ℂ) → ℂ) (hf_holo : DifferentiableOn ℂ f (TubeDomain (LShape r R)))
    (hf_bound : ∃ M : ℝ, ∀ z : Fin 2 → ℂ, ‖f z‖ ≤ M)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ z ∈ TubeDomain (LShapeConvexHull r R),
      ∃ (bound : (Fin 2 → ℝ) → ℝ), Integrable bound volume ∧ ∃ s ∈ 𝓝 z,
        (∀ᶠ w in 𝓝 z, AEStronglyMeasurable (fun ξ =>
          (bochner_fourier_transform_eps f ε (fun _ => r/2) ξ *
            Real.exp ((r/2) * ξ 0 + (r/2) * ξ 1)) *
          Complex.exp (I * (w 0 * ↑(ξ 0) + w 1 * ↑(ξ 1)))) volume) ∧
        Integrable (fun ξ =>
          (bochner_fourier_transform_eps f ε (fun _ => r/2) ξ *
            Real.exp ((r/2) * ξ 0 + (r/2) * ξ 1)) *
          Complex.exp (I * (z 0 * ↑(ξ 0) + z 1 * ↑(ξ 1)))) volume ∧
        AEStronglyMeasurable (fun ξ => fderiv ℂ (fun (w : Fin 2 → ℂ) =>
          (bochner_fourier_transform_eps f ε (fun _ => r/2) ξ *
            Real.exp ((r/2) * ξ 0 + (r/2) * ξ 1)) *
          Complex.exp (I * (w 0 * ↑(ξ 0) + w 1 * ↑(ξ 1)))) z) volume ∧
        (∀ᵐ ξ, ∀ w ∈ s, ‖fderiv ℂ (fun (w' : Fin 2 → ℂ) =>
          (bochner_fourier_transform_eps f ε (fun _ => r/2) ξ *
            Real.exp ((r/2) * ξ 0 + (r/2) * ξ 1)) *
          Complex.exp (I * (w' 0 * ↑(ξ 0) + w' 1 * ↑(ξ 1)))) w‖ ≤ bound ξ) := by
  intro z hz
  rcases bochner_F_eps_integrand_bound_integrable r R hr hR f hf_holo hf_bound ε hε z hz with
    ⟨bound, bound_int, s, hs, hint, hle⟩
  refine ⟨bound, bound_int, s, hs, ?_, hint, ?_, hle⟩
  · exact Filter.Eventually.of_forall (fun w =>
      bochner_F_eps_integrand_aestronglyMeasurable r R hr hR f hf_holo hf_bound ε hε w)
  · exact bochner_F_eps_integrand_fderiv_aestronglyMeasurable r R hr hR f hf_holo hf_bound ε hε z

lemma bochner_F_eps_holo (r R : ℝ) (hr : 0 < r) (hR : r < R)
    (f : (Fin 2 → ℂ) → ℂ) (hf_holo : DifferentiableOn ℂ f (TubeDomain (LShape r R)))
    (hf_bound : ∃ M : ℝ, ∀ z : Fin 2 → ℂ, ‖f z‖ ≤ M)
    (ε : ℝ) (hε : 0 < ε) :
    DifferentiableOn ℂ (bochner_F_eps f ε r R) (TubeDomain (LShapeConvexHull r R)) := by
  let c : (Fin 2 → ℝ) → ℂ := fun ξ =>
    bochner_fourier_transform_eps f ε (fun _ => r / 2) ξ * ↑(Real.exp (r / 2 * ξ 0 + r / 2 * ξ 1))
  have h_dom := bochner_F_eps_integrand_dom r R hr hR f hf_holo hf_bound ε hε
  have h_int := bochner_fourier_integral_holo_of_bound c (TubeDomain (LShapeConvexHull r R)) h_dom
  unfold bochner_F_eps
  have h1 : DifferentiableOn ℂ
      (fun z => (2 * Real.pi)⁻¹ *
        ∫ (ξ : Fin 2 → ℝ), c ξ * Complex.exp (I * (z 0 * ↑(ξ 0) + z 1 * ↑(ξ 1))))
      (TubeDomain (LShapeConvexHull r R)) := h_int.const_mul _
  have h2 : DifferentiableOn ℂ
      (fun z => (2 * Real.pi)⁻¹ * ((2 * Real.pi)⁻¹ *
        ∫ (ξ : Fin 2 → ℝ), c ξ * Complex.exp (I * (z 0 * ↑(ξ 0) + z 1 * ↑(ξ 1)))))
      (TubeDomain (LShapeConvexHull r R)) := h1.const_mul _
  have h_eq : (fun z : Fin 2 → ℂ => (2 * Real.pi)⁻¹ * (2 * Real.pi)⁻¹ * ∫ (ξ : Fin 2 → ℝ),
      (bochner_fourier_transform_eps f ε (fun x => r / 2) ξ *
        Real.exp (r / 2 * ξ 0 + r / 2 * ξ 1)) *
        Complex.exp (I * (z 0 * ↑(ξ 0) + z 1 * ↑(ξ 1)))) =
      (fun z => (2 * Real.pi)⁻¹ * ((2 * Real.pi)⁻¹ *
        ∫ (ξ : Fin 2 → ℝ), c ξ * Complex.exp (I * (z 0 * ↑(ξ 0) + z 1 * ↑(ξ 1))))) := by
    ext z
    ring
  rw [h_eq]
  exact h2

lemma bochner_F_eps_eq_standard_fourier_inv (r R : ℝ) (hr : 0 < r) (hR : r < R)
    (f : (Fin 2 → ℂ) → ℂ) (hf_holo : DifferentiableOn ℂ f (TubeDomain (LShape r R)))
    (hf_bound : ∃ M : ℝ, ∀ z : Fin 2 → ℂ, ‖f z‖ ≤ M)
    (ε : ℝ) (hε : 0 < ε)
    (z : Fin 2 → ℂ) (hz : z ∈ TubeDomain (LShape r R)) :
    bochner_F_eps f ε r R z =
    (2 * Real.pi)⁻¹ * (2 * Real.pi)⁻¹ * ∫ (ξ : Fin 2 → ℝ),
      bochner_fourier_transform_eps f ε (fun i => (z i).im) ξ *
      Complex.exp (I * (↑(z 0).re * ↑(ξ 0) + ↑(z 1).re * ↑(ξ 1))) := by
  let y : Fin 2 → ℝ := fun i => (z i).im
  let x : Fin 2 → ℝ := fun i => (z i).re
  have hy : y ∈ LShape r R := hz
  have hy_tube : (fun i => ↑(0 : ℝ) + I * ↑(y i)) ∈ TubeDomain (LShape r R) := by
    simp [TubeDomain, y, hy]
  have hy0 : (fun _ : Fin 2 => r / 2) ∈ LShape r R := by
    unfold LShape
    left
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hy0_tube :
      (fun i => ↑(0 : ℝ) + I * ↑((fun _ : Fin 2 => r / 2) i)) ∈ TubeDomain (LShape r R) := by
    simp [TubeDomain, hy0]
  unfold bochner_F_eps
  congr 1
  congr 1
  ext ξ
  have h_shift := bochner_fourier_transform_shift_eps r R hr hR f hf_holo hf_bound ε hε
    (fun _ => r/2) y hy0_tube hy_tube ξ
  have h_exp :
      (bochner_fourier_transform_eps f ε (fun _ => r / 2) ξ *
        ↑(Real.exp (r / 2 * ξ 0 + r / 2 * ξ 1))) *
        Complex.exp (I * (z 0 * ↑(ξ 0) + z 1 * ↑(ξ 1))) =
      bochner_fourier_transform_eps f ε y ξ *
      Complex.exp (I * (↑(z 0).re * ↑(ξ 0) + ↑(z 1).re * ↑(ξ 1))) := by
    rw [h_shift]
    rw [mul_assoc]
    congr 1
    have hz_rep : ∀ i, z i = ↑(x i) + I * ↑(y i) := by
      intro i
      dsimp [x, y]
      rw [mul_comm I ↑(z i).im, Complex.re_add_im]
    have h_cancel := fourier_inversion_integrand_cancel x y ξ
    have h_z0 : z 0 = ↑(x 0) + I * ↑(y 0) := hz_rep 0
    have h_z1 : z 1 = ↑(x 1) + I * ↑(y 1) := hz_rep 1
    rw [← h_z0, ← h_z1] at h_cancel
    exact h_cancel
  exact h_exp

noncomputable def fourier_transform_2d (φ : (Fin 2 → ℝ) → ℂ) (ξ : Fin 2 → ℝ) : ℂ :=
  ∫ (x : Fin 2 → ℝ), φ x * Complex.exp (-I * (↑(x 0) * ↑(ξ 0) + ↑(x 1) * ↑(ξ 1)))

lemma bochner_fourier_transform_eps_eq (f : (Fin 2 → ℂ) → ℂ) (ε : ℝ) (y : Fin 2 → ℝ) :
    bochner_fourier_transform_eps f ε y =
    fourier_transform_2d (fun x => bochner_f_eps f ε (fun i => ↑(x i) + I * ↑(y i))) := by
  ext ξ
  rfl

open Real FiniteDimensional VectorFourier

lemma euclidean_inner_eq (v w : EuclideanSpace ℝ (Fin 2)) :
    ⟪v, w⟫ = v 0 * w 0 + v 1 * w 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, mul_comm]

lemma euclidean_smul_apply (c : ℝ) (w : EuclideanSpace ℝ (Fin 2)) (i : Fin 2) :
    (c • w) i = c * w i := rfl

lemma exp_inner_eq (v w : EuclideanSpace ℝ (Fin 2)) :
    Complex.exp ((↑(-2 * π * ⟪v, w⟫) * Complex.I)) =
    Complex.exp (-I * (↑(v 0) * ↑(((2 * π) • w : EuclideanSpace ℝ (Fin 2)) 0) +
                       ↑(v 1) * ↑(((2 * π) • w : EuclideanSpace ℝ (Fin 2)) 1))) := by
  rw [euclidean_inner_eq]
  congr 1
  simp only [euclidean_smul_apply]
  push_cast
  ring

lemma integral_euclidean_eq_integral (g : (Fin 2 → ℝ) → ℂ) :
    ∫ v : EuclideanSpace ℝ (Fin 2), g v = ∫ x : Fin 2 → ℝ, g x :=
  (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2)).integral_comp' g

lemma integrable_euclidean_iff (g : (Fin 2 → ℝ) → ℂ) :
    Integrable (fun v : EuclideanSpace ℝ (Fin 2) => g v) ↔ Integrable g :=
  (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 2)).integrable_comp_emb
    (MeasurableEquiv.measurableEmbedding _)

lemma fourier_eq_fourier_transform_2d (φ : (Fin 2 → ℝ) → ℂ) (w : EuclideanSpace ℝ (Fin 2)) :
    𝓕 (fun v : EuclideanSpace ℝ (Fin 2) => φ v) w =
    fourier_transform_2d φ ((2 * π) • w) := by
  rw [fourier_eq']
  dsimp [fourier_transform_2d]
  rw [← integral_euclidean_eq_integral]
  congr 1
  ext v
  rw [exp_inner_eq v w]
  simp only [euclidean_smul_apply, mul_comm]

lemma euclidean_fourierInv_eq (g : EuclideanSpace ℝ (Fin 2) → ℂ) (x₀ : EuclideanSpace ℝ (Fin 2)) :
    𝓕⁻ g x₀ = ∫ w : EuclideanSpace ℝ (Fin 2),
      Complex.exp ((↑(2 * π * ⟪w, x₀⟫) * Complex.I)) * g w := by
  rw [fourierInv_eq]
  simp only [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]

lemma integral_comp_two_pi_smul (H : EuclideanSpace ℝ (Fin 2) → ℂ) :
    ∫ w : EuclideanSpace ℝ (Fin 2), H ((2 * π) • w) =
    (2 * Real.pi)⁻¹ * (2 * Real.pi)⁻¹ * ∫ ξ : EuclideanSpace ℝ (Fin 2), H ξ := by
  have hR : 0 ≤ 2 * Real.pi := by positivity
  have h := Measure.integral_comp_smul_of_nonneg
    (μ := (volume : Measure (EuclideanSpace ℝ (Fin 2)))) H (2 * Real.pi) (hR := hR)
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) = 2 := by simp
  rw [hdim] at h
  rw [h]
  simp only [Complex.real_smul]
  push_cast
  ring

lemma fourier_comp_toLp_integrable (φ : (Fin 2 → ℝ) → ℂ)
    (hφ_hat_int : Integrable (fourier_transform_2d φ)) :
    Integrable (𝓕 (fun v : EuclideanSpace ℝ (Fin 2) => φ v)) := by
  have h_ne : (2 * Real.pi) ≠ 0 := by positivity
  have h_hat_euc : Integrable (fun ξ : EuclideanSpace ℝ (Fin 2) => fourier_transform_2d φ ξ) :=
    (integrable_euclidean_iff (fourier_transform_2d φ)).2 hφ_hat_int
  have h_hat_smul : Integrable (fun w : EuclideanSpace ℝ (Fin 2) =>
      fourier_transform_2d φ (((2 * π) • w : EuclideanSpace ℝ (Fin 2)))) :=
    h_hat_euc.comp_smul h_ne
  have h_F_f : 𝓕 (fun v : EuclideanSpace ℝ (Fin 2) => φ v) =
      fun w : EuclideanSpace ℝ (Fin 2) =>
        fourier_transform_2d φ (((2 * π) • w : EuclideanSpace ℝ (Fin 2))) := by
    ext w
    exact fourier_eq_fourier_transform_2d φ w
  rw [h_F_f]
  exact h_hat_smul

lemma fourierInv_fourier_eval (φ : (Fin 2 → ℝ) → ℂ) (x₀ : Fin 2 → ℝ)
    (hφ_cont : Continuous φ)
    (hφ_int : Integrable φ)
    (hφ_hat_int : Integrable (fourier_transform_2d φ)) :
    𝓕⁻ (𝓕 (fun v : EuclideanSpace ℝ (Fin 2) => φ v)) (WithLp.toLp 2 x₀) = φ x₀ := by
  let f : EuclideanSpace ℝ (Fin 2) → ℂ := fun v => φ v
  have hf_cont : Continuous f := hφ_cont.comp (PiLp.continuous_ofLp (p := 2) (β := fun _ => ℝ))
  have hf_int : Integrable f := (integrable_euclidean_iff φ).2 hφ_int
  have h_F_int : Integrable (𝓕 f) := fourier_comp_toLp_integrable φ hφ_hat_int
  have h_inv := Continuous.fourierInv_fourier_eq hf_cont hf_int h_F_int
  have h_inv_at := congr_fun h_inv (WithLp.toLp 2 x₀)
  exact h_inv_at

lemma fourierInv_as_integral_2d (φ : (Fin 2 → ℝ) → ℂ) (x₀ : Fin 2 → ℝ) :
    𝓕⁻ (𝓕 (fun v : EuclideanSpace ℝ (Fin 2) => φ v)) (WithLp.toLp 2 x₀) =
    (2 * Real.pi)⁻¹ * (2 * Real.pi)⁻¹ * ∫ (ξ : Fin 2 → ℝ),
      fourier_transform_2d φ ξ *
      Complex.exp (I * (↑(x₀ 0) * ↑(ξ 0) + ↑(x₀ 1) * ↑(ξ 1))) := by
  let x₀_euc : EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2 x₀
  let f : EuclideanSpace ℝ (Fin 2) → ℂ := fun v => φ v
  rw [euclidean_fourierInv_eq]
  let H_fin : (Fin 2 → ℝ) → ℂ := fun ξ =>
    Complex.exp (I * (↑(x₀ 0) * ↑(ξ 0) + ↑(x₀ 1) * ↑(ξ 1))) * fourier_transform_2d φ ξ
  let H : EuclideanSpace ℝ (Fin 2) → ℂ := fun ξ => H_fin ξ
  have h_int_H : (∫ (w : EuclideanSpace ℝ (Fin 2)),
      Complex.exp (↑(2 * π * ⟪w, x₀_euc⟫) * I) * 𝓕 f w) =
      ∫ (w : EuclideanSpace ℝ (Fin 2)), H ((2 * π) • w) := by
    congr 1
    ext w
    have h_F_f : 𝓕 f w = fourier_transform_2d φ (((2 * π) • w : EuclideanSpace ℝ (Fin 2))) :=
      fourier_eq_fourier_transform_2d φ w
    rw [h_F_f]
    dsimp [H, H_fin]
    congr 1
    rw [euclidean_inner_eq]
    congr 1
    simp only [x₀_euc]
    push_cast
    ring
  rw [h_int_H]
  rw [integral_comp_two_pi_smul H]
  congr 1
  dsimp [H]
  rw [integral_euclidean_eq_integral H_fin]
  congr 1
  ext ξ
  ring

lemma fourier_inversion_2d (φ : (Fin 2 → ℝ) → ℂ) (x₀ : Fin 2 → ℝ)
    (hφ_cont : Continuous φ)
    (hφ_int : Integrable φ)
    (hφ_hat_int : Integrable (fourier_transform_2d φ)) :
    (2 * Real.pi)⁻¹ * (2 * Real.pi)⁻¹ * ∫ (ξ : Fin 2 → ℝ),
      fourier_transform_2d φ ξ *
      Complex.exp (I * (↑(x₀ 0) * ↑(ξ 0) + ↑(x₀ 1) * ↑(ξ 1))) = φ x₀ := by
  rw [← fourierInv_as_integral_2d]
  exact fourierInv_fourier_eval φ x₀ hφ_cont hφ_int hφ_hat_int

lemma bochner_f_eps_cont_of_holo (r R : ℝ) (f : (Fin 2 → ℂ) → ℂ)
    (hf_holo : DifferentiableOn ℂ f (TubeDomain (LShape r R)))
    (ε : ℝ) (y : Fin 2 → ℝ) (hy : y ∈ LShape r R) :
    Continuous (fun x : Fin 2 → ℝ => bochner_f_eps f ε (fun i => ↑(x i) + I * ↑(y i))) := by
  have hf_cont := bochner_f_cont_of_holo r R f hf_holo y hy
  unfold bochner_f_eps
  have h_exp : Continuous (fun x : Fin 2 → ℝ =>
      Complex.exp (-↑ε * (((x 0 : ℂ) + I * (y 0 : ℂ)) ^ 2 + ((x 1 : ℂ) + I * (y 1 : ℂ)) ^ 2))) := by
    apply Complex.continuous_exp.comp
    apply continuous_const.mul
    apply Continuous.add
    · exact (((Complex.continuous_ofReal.comp (continuous_apply 0)).add continuous_const).pow 2)
    · exact (((Complex.continuous_ofReal.comp (continuous_apply 1)).add continuous_const).pow 2)
  exact hf_cont.mul h_exp

lemma bochner_f_eps_eq_integrand_zero (f : (Fin 2 → ℂ) → ℂ) (ε : ℝ) (z : Fin 2 → ℂ) :
    bochner_integrand_F f ε 0 z = bochner_f_eps f ε z := by
  unfold bochner_integrand_F
  simp

lemma bochner_f_eps_integrable_of_holo (r R : ℝ) (f : (Fin 2 → ℂ) → ℂ)
    (hf_holo : DifferentiableOn ℂ f (TubeDomain (LShape r R)))
    (hf_bound : ∃ M : ℝ, ∀ z : Fin 2 → ℂ, ‖f z‖ ≤ M)
    (ε : ℝ) (hε : 0 < ε) (y : Fin 2 → ℝ) (hy : y ∈ LShape r R) :
    Integrable (fun x : Fin 2 → ℝ => bochner_f_eps f ε (fun i => ↑(x i) + I * ↑(y i))) := by
  have hint := bochner_integrand_integrable_2d r R f hf_holo hf_bound ε hε 0 y hy
  have heq : (fun x : Fin 2 → ℝ => bochner_integrand_F f ε 0 (fun i => ↑(x i) + I * ↑(y i))) =
      (fun x : Fin 2 → ℝ => bochner_f_eps f ε (fun i => ↑(x i) + I * ↑(y i))) := by
    ext x
    exact bochner_f_eps_eq_integrand_zero f ε (fun i => ↑(x i) + I * ↑(y i))
  rw [heq] at hint
  exact hint

lemma bochner_fourier_transform_eps_integrable (r R : ℝ) (hr : 0 < r) (hR : r < R)
    (f : (Fin 2 → ℂ) → ℂ) (hf_holo : DifferentiableOn ℂ f (TubeDomain (LShape r R)))
    (hf_bound : ∃ M : ℝ, ∀ z : Fin 2 → ℂ, ‖f z‖ ≤ M)
    (ε : ℝ) (hε : 0 < ε) (y : Fin 2 → ℝ) (hy : y ∈ LShape r R) :
    Integrable
      (fourier_transform_2d (fun x => bochner_f_eps f ε (fun i => ↑(x i) + I * ↑(y i)))) := by
  have h_eq : fourier_transform_2d (fun x => bochner_f_eps f ε (fun i => ↑(x i) + I * ↑(y i))) =
      bochner_fourier_transform_eps f ε y := (bochner_fourier_transform_eps_eq f ε y).symm
  rw [h_eq]
  have hy_hull : y ∈ LShapeConvexHull r R := subset_convexHull _ _ hy
  rcases bochner_c_eps_local_exp_decay r R hr hR f hf_holo hf_bound ε hε y hy_hull with
    ⟨C, δ, hC, hδ_pos, h_decay⟩
  have h_bound : Integrable (fun ξ : Fin 2 → ℝ => C * Real.exp (-δ * (|ξ 0| + |ξ 1|))) volume :=
    (integrable_exp_neg_abs_2d δ hδ_pos).const_mul C
  have hint := bochner_f_eps_integrable_of_holo r R f hf_holo hf_bound ε hε y hy
  have h_cont_c : Continuous (bochner_fourier_transform_eps f ε y) :=
    continuous_bochner_fourier_transform_eps f ε y hint
  have h_meas : AEStronglyMeasurable (bochner_fourier_transform_eps f ε y) volume :=
    h_cont_c.aestronglyMeasurable
  have h_le : ∀ᵐ ξ,
      ‖bochner_fourier_transform_eps f ε y ξ‖ ≤ C * Real.exp (-δ * (|ξ 0| + |ξ 1|)) := by
    apply ae_of_all
    intro ξ
    have hy_tube : (fun i => ↑(0 : ℝ) + Complex.I * ↑(y i)) ∈ TubeDomain (LShape r R) :=
      (mem_TubeDomain_pure_imag (LShape r R) y).mpr hy
    have h_norm_shift := bochner_c_eps_norm_le r R hr hR f hf_holo hf_bound ε hε y hy_tube ξ
    have h_norm_prod :
        ‖bochner_fourier_transform_eps f ε y ξ * ↑(Real.exp (y 0 * ξ 0 + y 1 * ξ 1))‖ =
        ‖bochner_fourier_transform_eps f ε y ξ‖ * Real.exp (y 0 * ξ 0 + y 1 * ξ 1) := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    have h_norm_prod_r2 :
        ‖bochner_fourier_transform_eps f ε (fun _ => r/2) ξ *
          ↑(Real.exp ((r/2) * ξ 0 + (r/2) * ξ 1))‖ =
        ‖bochner_fourier_transform_eps f ε y ξ‖ * Real.exp (y 0 * ξ 0 + y 1 * ξ 1) := by
      rw [h_norm_shift, h_norm_prod]
    have h_dec := h_decay ξ
    rw [h_norm_prod_r2] at h_dec
    calc ‖bochner_fourier_transform_eps f ε y ξ‖
      _ = (‖bochner_fourier_transform_eps f ε y ξ‖ * Real.exp (y 0 * ξ 0 + y 1 * ξ 1)) *
          Real.exp (-(y 0 * ξ 0 + y 1 * ξ 1)) := by
        rw [mul_assoc, ← Real.exp_add]
        have : (y 0 * ξ 0 + y 1 * ξ 1) + -(y 0 * ξ 0 + y 1 * ξ 1) = 0 := by ring
        rw [this, Real.exp_zero, mul_one]
      _ ≤ C * Real.exp (-δ * (|ξ 0| + |ξ 1|)) := h_dec
  exact Integrable.mono' h_bound h_meas h_le

lemma bochner_fourier_inversion_2d (r R : ℝ) (hr : 0 < r) (hR : r < R)
    (f : (Fin 2 → ℂ) → ℂ)
    (hf_holo : DifferentiableOn ℂ f (TubeDomain (LShape r R)))
    (hf_bound : ∃ M : ℝ, ∀ z : Fin 2 → ℂ, ‖f z‖ ≤ M)
    (ε : ℝ) (hε : 0 < ε)
    (y : Fin 2 → ℝ) (hy : y ∈ LShape r R) (x₀ : Fin 2 → ℝ) :
    (2 * Real.pi)⁻¹ * (2 * Real.pi)⁻¹ * ∫ (ξ : Fin 2 → ℝ),
      bochner_fourier_transform_eps f ε y ξ *
      Complex.exp (I * (↑(x₀ 0) * ↑(ξ 0) + ↑(x₀ 1) * ↑(ξ 1))) =
    bochner_f_eps f ε (fun i => ↑(x₀ i) + I * ↑(y i)) := by
  have h_eq : bochner_fourier_transform_eps f ε y =
      fourier_transform_2d (fun x => bochner_f_eps f ε (fun i => ↑(x i) + I * ↑(y i))) :=
    bochner_fourier_transform_eps_eq f ε y
  rw [h_eq]
  let φ : (Fin 2 → ℝ) → ℂ := fun x => bochner_f_eps f ε (fun i => ↑(x i) + I * ↑(y i))
  exact fourier_inversion_2d φ x₀
    (bochner_f_eps_cont_of_holo r R f hf_holo ε y hy)
    (bochner_f_eps_integrable_of_holo r R f hf_holo hf_bound ε hε y hy)
    (bochner_fourier_transform_eps_integrable r R hr hR f hf_holo hf_bound ε hε y hy)

lemma bochner_F_eps_eq_f (r R : ℝ) (hr : 0 < r) (hR : r < R)
    (f : (Fin 2 → ℂ) → ℂ) (hf_holo : DifferentiableOn ℂ f (TubeDomain (LShape r R)))
    (hf_bound : ∃ M : ℝ, ∀ z : Fin 2 → ℂ, ‖f z‖ ≤ M)
    (ε : ℝ) (hε : 0 < ε) :
    EqOn (bochner_F_eps f ε r R) (bochner_f_eps f ε) (TubeDomain (LShape r R)) := by
  intro z hz
  rw [bochner_F_eps_eq_standard_fourier_inv r R hr hR f hf_holo hf_bound ε hε z hz]
  have hy : (fun i => (z i).im) ∈ LShape r R := hz
  have h_inv := bochner_fourier_inversion_2d r R hr hR f hf_holo hf_bound ε hε
    (fun i => (z i).im) hy (fun i => (z i).re)
  have hz_rep : (fun i => ↑((z i).re) + I * ↑((z i).im)) = z := by
    ext i
    rw [mul_comm I, Complex.re_add_im]
  rw [hz_rep] at h_inv
  exact h_inv

lemma bochner_f_eps_tendsto (f : (Fin 2 → ℂ) → ℂ) (z : Fin 2 → ℂ) :
    Tendsto (fun ε : ℝ => bochner_f_eps f ε z) (𝓝[>] 0) (𝓝 (f z)) := by
  unfold bochner_f_eps
  have h_exp : Tendsto (fun ε : ℝ => Complex.exp (-↑ε * (z 0 ^ 2 + z 1 ^ 2))) (𝓝[>] 0) (𝓝 1) := by
    have h_inner : Tendsto (fun ε : ℝ => - (ε : ℂ) * (z 0 ^ 2 + z 1 ^ 2)) (𝓝[>] 0) (𝓝 0) := by
      have h_cont : Continuous (fun ε : ℝ => - (ε : ℂ) * (z 0 ^ 2 + z 1 ^ 2)) :=
        (Complex.continuous_ofReal.neg).mul continuous_const
      have ht := h_cont.tendsto (0 : ℝ)
      simp only [Complex.ofReal_zero, neg_zero, zero_mul] at ht
      exact ht.mono_left nhdsWithin_le_nhds
    have h_exp_cont := Complex.continuous_exp.tendsto (0 : ℂ)
    rw [Complex.exp_zero] at h_exp_cont
    exact h_exp_cont.comp h_inner
  have h_mul := h_exp.const_mul (f z)
  rw [mul_one] at h_mul
  exact h_mul

lemma bochner_F_eps_tendsto_on_tube (r R : ℝ) (f : (Fin 2 → ℂ) → ℂ)
    (h_eq_eps : ∀ ε > 0, EqOn (bochner_F_eps f ε r R) (bochner_f_eps f ε) (TubeDomain (LShape r R)))
    (z : Fin 2 → ℂ) (hz : z ∈ TubeDomain (LShape r R)) :
    Tendsto (fun ε : ℝ => bochner_F_eps f ε r R z) (𝓝[>] 0) (𝓝 (f z)) := by
  have h_eq : (fun ε : ℝ => bochner_F_eps f ε r R z) =ᶠ[𝓝[>] 0]
      (fun ε : ℝ => bochner_f_eps f ε z) := by
    apply eventually_nhdsWithin_of_forall
    intro ε hε
    exact h_eq_eps ε hε hz
  exact (bochner_f_eps_tendsto f z).congr' h_eq.symm

noncomputable def bochner_F_limit (f : (Fin 2 → ℂ) → ℂ) (r R : ℝ) (z : Fin 2 → ℂ) : ℂ :=
  limUnder (𝓝[>] (0 : ℝ)) (fun ε => bochner_F_eps f ε r R z)

lemma limUnder_congr {X α : Type*} [TopologicalSpace X] [Nonempty X]
    {F : Filter α} {g h : α → X} (h_eq : g =ᶠ[F] h) :
    limUnder F g = limUnder F h := by
  dsimp [limUnder]
  rw [Filter.map_congr h_eq]

lemma bochner_F_limit_eq_on_tube (r R : ℝ) (f : (Fin 2 → ℂ) → ℂ)
    (h_eq_eps : ∀ ε > 0,
      EqOn (bochner_F_eps f ε r R) (bochner_f_eps f ε) (TubeDomain (LShape r R))) :
    EqOn (bochner_F_limit f r R) f (TubeDomain (LShape r R)) := by
  intro z hz
  dsimp [bochner_F_limit]
  have h_tendsto := bochner_F_eps_tendsto_on_tube r R f h_eq_eps z hz
  exact h_tendsto.limUnder_eq

lemma differentiableOn_cauchy_integral {f : ℂ → ℂ} {c : ℂ} {R : NNReal}
    (hf : CircleIntegrable f c R) (hR : 0 < R) :
    DifferentiableOn ℂ
      (fun w => (2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - w)⁻¹ • f z) (Metric.ball c R) := by
  intro w hw
  have hw' : w ∈ Metric.eball c R := by
    rw [Metric.eball_coe]
    exact hw
  have h_series := hasFPowerSeriesOn_cauchy_integral hf hR
  have h_an : AnalyticAt ℂ (fun w => (2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - w)⁻¹ • f z) w :=
    h_series.analyticAt_of_mem hw'
  exact h_an.differentiableAt.differentiableWithinAt

lemma differentiableOn_circleIntegral_sub_inv_smul {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hf : CircleIntegrable f c R) (hR : 0 < R) :
    DifferentiableOn ℂ
      (fun w => (2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - w)⁻¹ • f z) (Metric.ball c R) := by
  lift R to NNReal using hR.le
  exact differentiableOn_cauchy_integral hf hR

lemma differentiableAt_circleIntegral_sub_inv_smul {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hf : CircleIntegrable f c R) (hR : 0 < R) {w : ℂ} (hw : w ∈ Metric.ball c R) :
    DifferentiableAt ℂ (fun w => (2 * π * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - w)⁻¹ • f z) w := by
  have hd := differentiableOn_circleIntegral_sub_inv_smul hf hR
  exact hd.differentiableAt (Metric.isOpen_ball.mem_nhds hw)

lemma isOpen_slice0 {U : Set (Fin 2 → ℂ)} (hU : IsOpen U) (z : Fin 2 → ℂ) :
    IsOpen {w : ℂ | (fun i => if i = 0 then w else z 1) ∈ U} := by
  let g : ℂ → (Fin 2 → ℂ) := fun w i => if i = 0 then w else z 1
  have hg : Continuous g := by
    apply continuous_pi
    intro i
    dsimp [g]
    split_ifs
    · exact continuous_id
    · exact continuous_const
  exact hU.preimage hg

lemma exists_ball_subset_slice0 {U : Set (Fin 2 → ℂ)} (hU : IsOpen U)
    (z : Fin 2 → ℂ) (hz : z ∈ U) :
    ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball (z 0) ρ ⊆
      {w : ℂ | (fun i => if i = 0 then w else z 1) ∈ U} := by
  have h_open := isOpen_slice0 hU z
  have hz0_mem : z 0 ∈ {w : ℂ | (fun i => if i = 0 then w else z 1) ∈ U} := by
    dsimp
    have hz_eq : (fun i => if i = 0 then z 0 else z 1) = z := by
      ext i
      fin_cases i <;> simp
    rw [hz_eq]
    exact hz
  rcases Metric.isOpen_iff.mp h_open (z 0) hz0_mem with ⟨ρ, hρ, h_sub⟩
  exact ⟨ρ, hρ, h_sub⟩

lemma isOpen_slice1 {U : Set (Fin 2 → ℂ)} (hU : IsOpen U) (z : Fin 2 → ℂ) :
    IsOpen {w : ℂ | (fun i => if i = 1 then w else z 0) ∈ U} := by
  let g : ℂ → (Fin 2 → ℂ) := fun w i => if i = 1 then w else z 0
  have hg : Continuous g := by
    apply continuous_pi
    intro i
    dsimp [g]
    split_ifs
    · exact continuous_id
    · exact continuous_const
  exact hU.preimage hg

lemma exists_ball_subset_slice1 {U : Set (Fin 2 → ℂ)} (hU : IsOpen U)
    (z : Fin 2 → ℂ) (hz : z ∈ U) :
    ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball (z 1) ρ ⊆
      {w : ℂ | (fun i => if i = 1 then w else z 0) ∈ U} := by
  have h_open := isOpen_slice1 hU z
  have hz1_mem : z 1 ∈ {w : ℂ | (fun i => if i = 1 then w else z 0) ∈ U} := by
    dsimp
    have hz_eq : (fun i => if i = 1 then z 1 else z 0) = z := by
      ext i
      fin_cases i <;> simp
    rw [hz_eq]
    exact hz
  rcases Metric.isOpen_iff.mp h_open (z 1) hz1_mem with ⟨ρ, hρ, h_sub⟩
  exact ⟨ρ, hρ, h_sub⟩

lemma differentiable_slice_of_cauchy_representation (U : Set (Fin 2 → ℂ))
    (F : (Fin 2 → ℂ) → ℂ)
    (h_slice0 : ∀ z ∈ U, ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧
      z 0 ∈ Metric.ball c R ∧
      ∃ g : ℂ → ℂ, CircleIntegrable g c R ∧
        ∀ w ∈ Metric.ball c R, F (fun i => if i = 0 then w else z 1) =
          (2 * π * I : ℂ)⁻¹ • ∮ ζ in C(c, R), (ζ - w)⁻¹ • g ζ) :
    ∀ z ∈ U, DifferentiableAt ℂ (fun w => F (fun i => if i = 0 then w else z 1)) (z 0) := by
  intro z hz
  rcases h_slice0 z hz with ⟨c, R, hR, hz0, g, hg, hF⟩
  have hd := differentiableAt_circleIntegral_sub_inv_smul hg hR hz0
  have h_nhds : Metric.ball c R ∈ 𝓝 (z 0) := Metric.isOpen_ball.mem_nhds hz0
  have h_eq : (fun w => F (fun i => if i = 0 then w else z 1)) =ᶠ[𝓝 (z 0)]
      (fun w => (2 * π * I : ℂ)⁻¹ • ∮ ζ in C(c, R), (ζ - w)⁻¹ • g ζ) := by
    apply Filter.eventually_of_mem h_nhds
    intro w hw
    exact hF w hw
  exact hd.congr_of_eventuallyEq h_eq

lemma differentiable_slice1_of_cauchy_representation (U : Set (Fin 2 → ℂ))
    (F : (Fin 2 → ℂ) → ℂ)
    (h_slice1 : ∀ z ∈ U, ∃ c : ℂ, ∃ R : ℝ, 0 < R ∧
      z 1 ∈ Metric.ball c R ∧
      ∃ g : ℂ → ℂ, CircleIntegrable g c R ∧
        ∀ w ∈ Metric.ball c R, F (fun i => if i = 1 then w else z 0) =
          (2 * π * I : ℂ)⁻¹ • ∮ ζ in C(c, R), (ζ - w)⁻¹ • g ζ) :
    ∀ z ∈ U, DifferentiableAt ℂ (fun w => F (fun i => if i = 1 then w else z 0)) (z 1) := by
  intro z hz
  rcases h_slice1 z hz with ⟨c, R, hR, hz1, g, hg, hF⟩
  have hd := differentiableAt_circleIntegral_sub_inv_smul hg hR hz1
  have h_nhds : Metric.ball c R ∈ 𝓝 (z 1) := Metric.isOpen_ball.mem_nhds hz1
  have h_eq : (fun w => F (fun i => if i = 1 then w else z 0)) =ᶠ[𝓝 (z 1)]
      (fun w => (2 * π * I : ℂ)⁻¹ • ∮ ζ in C(c, R), (ζ - w)⁻¹ • g ζ) := by
    apply Filter.eventually_of_mem h_nhds
    intro w hw
    exact hF w hw
  exact hd.congr_of_eventuallyEq h_eq

lemma differentiableOn_of_differentiableAt_all (U : Set (Fin 2 → ℂ))
    (F : (Fin 2 → ℂ) → ℂ) (h_diff : ∀ z ∈ U, DifferentiableAt ℂ F z) :
    DifferentiableOn ℂ F U := by
  intro z hz
  exact (h_diff z hz).differentiableWithinAt

lemma bochner_F_eps_slice0_cauchy_rep (r R : ℝ) (_hr : 0 < r) (_hR : r < R)
    (f : (Fin 2 → ℂ) → ℂ)
    (h_holo_eps : ∀ ε > 0,
      DifferentiableOn ℂ (bochner_F_eps f ε r R) (TubeDomain (LShapeConvexHull r R)))
    (z : Fin 2 → ℂ) (hz : z ∈ TubeDomain (LShapeConvexHull r R))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℂ, ∃ ρ : ℝ, 0 < ρ ∧
      z 0 ∈ Metric.ball c ρ ∧
      let F_slice := fun w => bochner_F_eps f ε r R (fun i => if i = 0 then w else z 1)
      CircleIntegrable F_slice c ρ ∧
      ∀ w ∈ Metric.ball c ρ, F_slice w =
        (2 * ↑Real.pi * Complex.I : ℂ)⁻¹ • ∮ ζ in C(c, ρ), (ζ - w)⁻¹ • F_slice ζ := by
  have hU_open : IsOpen (TubeDomain (LShapeConvexHull r R)) :=
    isOpen_TubeDomain (isOpen_LShapeConvexHull r R)
  rcases exists_ball_subset_slice0 hU_open z hz with ⟨ρ0, hρ0, h_sub0⟩
  let ρ := ρ0 / 2
  have hρ : 0 < ρ := half_pos hρ0
  refine ⟨z 0, ρ, hρ, Metric.mem_ball_self hρ, ?_⟩
  dsimp
  let F_slice := fun w => bochner_F_eps f ε r R (fun i => if i = 0 then w else z 1)
  have h_cball : Metric.closedBall (z 0) ρ ⊆ Metric.ball (z 0) ρ0 := by
    intro w hw
    rw [Metric.mem_closedBall] at hw
    rw [Metric.mem_ball]
    dsimp [ρ] at hw
    linarith
  have h_cball_sub : Metric.closedBall (z 0) ρ ⊆
      {w : ℂ | (fun i => if i = 0 then w else z 1) ∈ TubeDomain (LShapeConvexHull r R)} :=
    h_cball.trans h_sub0
  have h_diff_slice : DifferentiableOn ℂ F_slice (Metric.closedBall (z 0) ρ) := by
    let φ : ℂ → (Fin 2 → ℂ) := fun w i => if i = 0 then w else z 1
    have hφ_diff : Differentiable ℂ φ := by
      apply differentiable_pi.mpr
      intro i
      dsimp [φ]
      split_ifs
      · exact differentiable_id
      · exact differentiable_const _
    have h_comp : F_slice = (bochner_F_eps f ε r R) ∘ φ := rfl
    rw [h_comp]
    apply (h_holo_eps ε hε).comp hφ_diff.differentiableOn h_cball_sub
  have h_ci : CircleIntegrable F_slice (z 0) ρ := by
    apply ContinuousOn.circleIntegrable hρ.le
    exact h_diff_slice.continuousOn.mono Metric.sphere_subset_closedBall
  refine ⟨h_ci, ?_⟩
  intro w hw
  have h_cauchy := DifferentiableOn.circleIntegral_sub_inv_smul h_diff_slice hw
  have h_2piI_ne : (2 * ↑Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Complex.I_ne_zero, Real.pi_ne_zero]
  calc F_slice w
    _ = (2 * ↑Real.pi * Complex.I : ℂ)⁻¹ • ((2 * ↑Real.pi * Complex.I : ℂ) • F_slice w) := by
      rw [← mul_smul, inv_mul_cancel₀ h_2piI_ne, one_smul]
    _ = (2 * ↑Real.pi * Complex.I : ℂ)⁻¹ • ∮ ζ in C(z 0, ρ), (ζ - w)⁻¹ • F_slice ζ := by
      rw [h_cauchy]

lemma bochner_F_eps_slice1_cauchy_rep (r R : ℝ) (_hr : 0 < r) (_hR : r < R)
    (f : (Fin 2 → ℂ) → ℂ)
    (h_holo_eps : ∀ ε > 0,
      DifferentiableOn ℂ (bochner_F_eps f ε r R) (TubeDomain (LShapeConvexHull r R)))
    (z : Fin 2 → ℂ) (hz : z ∈ TubeDomain (LShapeConvexHull r R))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ c : ℂ, ∃ ρ : ℝ, 0 < ρ ∧
      z 1 ∈ Metric.ball c ρ ∧
      let F_slice := fun w => bochner_F_eps f ε r R (fun i => if i = 1 then w else z 0)
      CircleIntegrable F_slice c ρ ∧
      ∀ w ∈ Metric.ball c ρ, F_slice w =
        (2 * ↑Real.pi * Complex.I : ℂ)⁻¹ • ∮ ζ in C(c, ρ), (ζ - w)⁻¹ • F_slice ζ := by
  have hU_open : IsOpen (TubeDomain (LShapeConvexHull r R)) :=
    isOpen_TubeDomain (isOpen_LShapeConvexHull r R)
  rcases exists_ball_subset_slice1 hU_open z hz with ⟨ρ0, hρ0, h_sub0⟩
  let ρ := ρ0 / 2
  have hρ : 0 < ρ := half_pos hρ0
  refine ⟨z 1, ρ, hρ, Metric.mem_ball_self hρ, ?_⟩
  dsimp
  let F_slice := fun w => bochner_F_eps f ε r R (fun i => if i = 1 then w else z 0)
  have h_cball : Metric.closedBall (z 1) ρ ⊆ Metric.ball (z 1) ρ0 := by
    intro w hw
    rw [Metric.mem_closedBall] at hw
    rw [Metric.mem_ball]
    dsimp [ρ] at hw
    linarith
  have h_cball_sub : Metric.closedBall (z 1) ρ ⊆
      {w : ℂ | (fun i => if i = 1 then w else z 0) ∈ TubeDomain (LShapeConvexHull r R)} :=
    h_cball.trans h_sub0
  have h_diff_slice : DifferentiableOn ℂ F_slice (Metric.closedBall (z 1) ρ) := by
    let φ : ℂ → (Fin 2 → ℂ) := fun w i => if i = 1 then w else z 0
    have hφ_diff : Differentiable ℂ φ := by
      apply differentiable_pi.mpr
      intro i
      dsimp [φ]
      split_ifs
      · exact differentiable_id
      · exact differentiable_const _
    have h_comp : F_slice = (bochner_F_eps f ε r R) ∘ φ := rfl
    rw [h_comp]
    apply (h_holo_eps ε hε).comp hφ_diff.differentiableOn h_cball_sub
  have h_ci : CircleIntegrable F_slice (z 1) ρ := by
    apply ContinuousOn.circleIntegrable hρ.le
    exact h_diff_slice.continuousOn.mono Metric.sphere_subset_closedBall
  refine ⟨h_ci, ?_⟩
  intro w hw
  have h_cauchy := DifferentiableOn.circleIntegral_sub_inv_smul h_diff_slice hw
  have h_2piI_ne : (2 * ↑Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Complex.I_ne_zero, Real.pi_ne_zero]
  calc F_slice w
    _ = (2 * ↑Real.pi * Complex.I : ℂ)⁻¹ • ((2 * ↑Real.pi * Complex.I : ℂ) • F_slice w) := by
      rw [← mul_smul, inv_mul_cancel₀ h_2piI_ne, one_smul]
    _ = (2 * ↑Real.pi * Complex.I : ℂ)⁻¹ • ∮ ζ in C(z 1, ρ), (ζ - w)⁻¹ • F_slice ζ := by
      rw [h_cauchy]

lemma bochner_F_limit_slice0_cauchy_rep (r R : ℝ) (_hr : 0 < r) (_hR : r < R)
    (f : (Fin 2 → ℂ) → ℂ)
    (h_holo_eps : ∀ ε > 0,
      DifferentiableOn ℂ (bochner_F_eps f ε r R) (TubeDomain (LShapeConvexHull r R)))
    (h_slice0_lim_comm : ∀ z ∈ TubeDomain (LShapeConvexHull r R), ∀ c : ℂ, ∀ ρ > 0,
      CircleIntegrable (fun ζ => bochner_F_limit f r R (fun i => if i = 0 then ζ else z 1)) c ρ ∧
      ∀ w ∈ Metric.ball c ρ,
        limUnder (𝓝[>] 0) (fun ε => (2 * ↑Real.pi * Complex.I : ℂ)⁻¹ • ∮ ζ in C(c, ρ),
          (ζ - w)⁻¹ • bochner_F_eps f ε r R (fun i => if i = 0 then ζ else z 1)) =
        (2 * π * I : ℂ)⁻¹ • ∮ ζ in C(c, ρ),
          (ζ - w)⁻¹ • bochner_F_limit f r R (fun i => if i = 0 then ζ else z 1)) :
    ∀ z ∈ TubeDomain (LShapeConvexHull r R), ∃ c : ℂ, ∃ ρ : ℝ, 0 < ρ ∧
      z 0 ∈ Metric.ball c ρ ∧
      ∃ g : ℂ → ℂ, CircleIntegrable g c ρ ∧
        ∀ w ∈ Metric.ball c ρ, bochner_F_limit f r R (fun i => if i = 0 then w else z 1) =
          (2 * π * I : ℂ)⁻¹ • ∮ ζ in C(c, ρ), (ζ - w)⁻¹ • g ζ := by
  intro z hz
  have hU_open : IsOpen (TubeDomain (LShapeConvexHull r R)) :=
    isOpen_TubeDomain (isOpen_LShapeConvexHull r R)
  rcases exists_ball_subset_slice0 hU_open z hz with ⟨ρ0, hρ0, h_sub0⟩
  let ρ := ρ0 / 2
  have hρ : 0 < ρ := half_pos hρ0
  refine ⟨z 0, ρ, hρ, Metric.mem_ball_self hρ, ?_⟩
  let g : ℂ → ℂ := fun ζ => bochner_F_limit f r R (fun i => if i = 0 then ζ else z 1)
  refine ⟨g, (h_slice0_lim_comm z hz (z 0) ρ hρ).1, ?_⟩
  intro w hw
  dsimp [bochner_F_limit]
  have h_eq : (fun ε : ℝ =>
        bochner_F_eps f ε r R (fun i => if i = 0 then w else z 1)) =ᶠ[𝓝[>] 0]
      (fun ε => (2 * ↑Real.pi * Complex.I : ℂ)⁻¹ • ∮ ζ in C(z 0, ρ),
        (ζ - w)⁻¹ • bochner_F_eps f ε r R (fun i => if i = 0 then ζ else z 1)) := by
    apply eventually_nhdsWithin_of_forall
    intro ε hε
    have h_cball : Metric.closedBall (z 0) ρ ⊆ Metric.ball (z 0) ρ0 := by
      intro w' hw'
      rw [Metric.mem_closedBall] at hw'
      rw [Metric.mem_ball]
      dsimp [ρ] at hw'
      linarith
    have h_cball_sub : Metric.closedBall (z 0) ρ ⊆
        {w' : ℂ | (fun i => if i = 0 then w' else z 1) ∈ TubeDomain (LShapeConvexHull r R)} :=
      h_cball.trans h_sub0
    let F_slice := fun w' => bochner_F_eps f ε r R (fun i => if i = 0 then w' else z 1)
    have h_diff_slice : DifferentiableOn ℂ F_slice (Metric.closedBall (z 0) ρ) := by
      let φ : ℂ → (Fin 2 → ℂ) := fun w' i => if i = 0 then w' else z 1
      have hφ_diff : Differentiable ℂ φ := by
        apply differentiable_pi.mpr
        intro i
        dsimp [φ]
        split_ifs
        · exact differentiable_id
        · exact differentiable_const _
      have h_comp : F_slice = (bochner_F_eps f ε r R) ∘ φ := rfl
      rw [h_comp]
      apply (h_holo_eps ε hε).comp hφ_diff.differentiableOn h_cball_sub
    have h_cauchy := DifferentiableOn.circleIntegral_sub_inv_smul h_diff_slice hw
    have h_2piI_ne : (2 * ↑Real.pi * Complex.I : ℂ) ≠ 0 := by
      simp [Complex.I_ne_zero, Real.pi_ne_zero]
    calc F_slice w
      _ = (2 * ↑Real.pi * Complex.I : ℂ)⁻¹ • ((2 * ↑Real.pi * Complex.I : ℂ) • F_slice w) := by
        rw [← mul_smul, inv_mul_cancel₀ h_2piI_ne, one_smul]
      _ = (2 * ↑Real.pi * Complex.I : ℂ)⁻¹ • ∮ ζ in C(z 0, ρ), (ζ - w)⁻¹ • F_slice ζ := by
        rw [h_cauchy]
  rw [limUnder_congr h_eq]
  exact (h_slice0_lim_comm z hz (z 0) ρ hρ).2 w hw

lemma bochner_F_limit_slice1_cauchy_rep (r R : ℝ) (_hr : 0 < r) (_hR : r < R)
    (f : (Fin 2 → ℂ) → ℂ)
    (h_holo_eps : ∀ ε > 0,
      DifferentiableOn ℂ (bochner_F_eps f ε r R) (TubeDomain (LShapeConvexHull r R)))
    (h_slice1_lim_comm : ∀ z ∈ TubeDomain (LShapeConvexHull r R), ∀ c : ℂ, ∀ ρ > 0,
      CircleIntegrable (fun ζ => bochner_F_limit f r R (fun i => if i = 1 then ζ else z 0)) c ρ ∧
      ∀ w ∈ Metric.ball c ρ,
        limUnder (𝓝[>] 0) (fun ε => (2 * ↑Real.pi * Complex.I : ℂ)⁻¹ • ∮ ζ in C(c, ρ),
          (ζ - w)⁻¹ • bochner_F_eps f ε r R (fun i => if i = 1 then ζ else z 0)) =
        (2 * π * I : ℂ)⁻¹ • ∮ ζ in C(c, ρ),
          (ζ - w)⁻¹ • bochner_F_limit f r R (fun i => if i = 1 then ζ else z 0)) :
    ∀ z ∈ TubeDomain (LShapeConvexHull r R), ∃ c : ℂ, ∃ ρ : ℝ, 0 < ρ ∧
      z 1 ∈ Metric.ball c ρ ∧
      ∃ g : ℂ → ℂ, CircleIntegrable g c ρ ∧
        ∀ w ∈ Metric.ball c ρ, bochner_F_limit f r R (fun i => if i = 1 then w else z 0) =
          (2 * π * I : ℂ)⁻¹ • ∮ ζ in C(c, ρ), (ζ - w)⁻¹ • g ζ := by
  intro z hz
  have hU_open : IsOpen (TubeDomain (LShapeConvexHull r R)) :=
    isOpen_TubeDomain (isOpen_LShapeConvexHull r R)
  rcases exists_ball_subset_slice1 hU_open z hz with ⟨ρ0, hρ0, h_sub0⟩
  let ρ := ρ0 / 2
  have hρ : 0 < ρ := half_pos hρ0
  refine ⟨z 1, ρ, hρ, Metric.mem_ball_self hρ, ?_⟩
  let g : ℂ → ℂ := fun ζ => bochner_F_limit f r R (fun i => if i = 1 then ζ else z 0)
  refine ⟨g, (h_slice1_lim_comm z hz (z 1) ρ hρ).1, ?_⟩
  intro w hw
  dsimp [bochner_F_limit]
  have h_eq : (fun ε : ℝ =>
        bochner_F_eps f ε r R (fun i => if i = 1 then w else z 0)) =ᶠ[𝓝[>] 0]
      (fun ε => (2 * ↑Real.pi * Complex.I : ℂ)⁻¹ • ∮ ζ in C(z 1, ρ),
        (ζ - w)⁻¹ • bochner_F_eps f ε r R (fun i => if i = 1 then ζ else z 0)) := by
    apply eventually_nhdsWithin_of_forall
    intro ε hε
    have h_cball : Metric.closedBall (z 1) ρ ⊆ Metric.ball (z 1) ρ0 := by
      intro w' hw'
      rw [Metric.mem_closedBall] at hw'
      rw [Metric.mem_ball]
      dsimp [ρ] at hw'
      linarith
    have h_cball_sub : Metric.closedBall (z 1) ρ ⊆
        {w' : ℂ | (fun i => if i = 1 then w' else z 0) ∈ TubeDomain (LShapeConvexHull r R)} :=
      h_cball.trans h_sub0
    let F_slice := fun w' => bochner_F_eps f ε r R (fun i => if i = 1 then w' else z 0)
    have h_diff_slice : DifferentiableOn ℂ F_slice (Metric.closedBall (z 1) ρ) := by
      let φ : ℂ → (Fin 2 → ℂ) := fun w' i => if i = 1 then w' else z 0
      have hφ_diff : Differentiable ℂ φ := by
        apply differentiable_pi.mpr
        intro i
        dsimp [φ]
        split_ifs
        · exact differentiable_id
        · exact differentiable_const _
      have h_comp : F_slice = (bochner_F_eps f ε r R) ∘ φ := rfl
      rw [h_comp]
      apply (h_holo_eps ε hε).comp hφ_diff.differentiableOn h_cball_sub
    have h_cauchy := DifferentiableOn.circleIntegral_sub_inv_smul h_diff_slice hw
    have h_2piI_ne : (2 * ↑Real.pi * Complex.I : ℂ) ≠ 0 := by
      simp [Complex.I_ne_zero, Real.pi_ne_zero]
    calc F_slice w
      _ = (2 * ↑Real.pi * Complex.I : ℂ)⁻¹ • ((2 * ↑Real.pi * Complex.I : ℂ) • F_slice w) := by
        rw [← mul_smul, inv_mul_cancel₀ h_2piI_ne, one_smul]
      _ = (2 * ↑Real.pi * Complex.I : ℂ)⁻¹ • ∮ ζ in C(z 1, ρ), (ζ - w)⁻¹ • F_slice ζ := by
        rw [h_cauchy]
  rw [limUnder_congr h_eq]
  exact (h_slice1_lim_comm z hz (z 1) ρ hρ).2 w hw

lemma bochner_F_limit_slice0_diff (r R : ℝ) (hr : 0 < r) (hR : r < R)
    (f : (Fin 2 → ℂ) → ℂ)
    (h_holo_eps : ∀ ε > 0,
      DifferentiableOn ℂ (bochner_F_eps f ε r R) (TubeDomain (LShapeConvexHull r R)))
    (h_slice0_lim_comm : ∀ z ∈ TubeDomain (LShapeConvexHull r R), ∀ c : ℂ, ∀ ρ > 0,
      CircleIntegrable (fun ζ => bochner_F_limit f r R (fun i => if i = 0 then ζ else z 1)) c ρ ∧
      ∀ w ∈ Metric.ball c ρ,
        limUnder (𝓝[>] 0) (fun ε => (2 * ↑Real.pi * Complex.I : ℂ)⁻¹ • ∮ ζ in C(c, ρ),
          (ζ - w)⁻¹ • bochner_F_eps f ε r R (fun i => if i = 0 then ζ else z 1)) =
        (2 * π * I : ℂ)⁻¹ • ∮ ζ in C(c, ρ),
          (ζ - w)⁻¹ • bochner_F_limit f r R (fun i => if i = 0 then ζ else z 1))
    (z : Fin 2 → ℂ) (hz : z ∈ TubeDomain (LShapeConvexHull r R)) :
    DifferentiableAt ℂ
      (fun w => bochner_F_limit f r R (fun i => if i = 0 then w else z 1)) (z 0) := by
  have h_rep := bochner_F_limit_slice0_cauchy_rep r R hr hR f h_holo_eps h_slice0_lim_comm
  exact differentiable_slice_of_cauchy_representation (TubeDomain (LShapeConvexHull r R))
    (bochner_F_limit f r R) h_rep z hz

lemma bochner_F_limit_slice1_diff (r R : ℝ) (hr : 0 < r) (hR : r < R)
    (f : (Fin 2 → ℂ) → ℂ)
    (h_holo_eps : ∀ ε > 0,
      DifferentiableOn ℂ (bochner_F_eps f ε r R) (TubeDomain (LShapeConvexHull r R)))
    (h_slice1_lim_comm : ∀ z ∈ TubeDomain (LShapeConvexHull r R), ∀ c : ℂ, ∀ ρ > 0,
      CircleIntegrable (fun ζ => bochner_F_limit f r R (fun i => if i = 1 then ζ else z 0)) c ρ ∧
      ∀ w ∈ Metric.ball c ρ,
        limUnder (𝓝[>] 0) (fun ε => (2 * ↑Real.pi * Complex.I : ℂ)⁻¹ • ∮ ζ in C(c, ρ),
          (ζ - w)⁻¹ • bochner_F_eps f ε r R (fun i => if i = 1 then ζ else z 0)) =
        (2 * π * I : ℂ)⁻¹ • ∮ ζ in C(c, ρ),
          (ζ - w)⁻¹ • bochner_F_limit f r R (fun i => if i = 1 then ζ else z 0))
    (z : Fin 2 → ℂ) (hz : z ∈ TubeDomain (LShapeConvexHull r R)) :
    DifferentiableAt ℂ
      (fun w => bochner_F_limit f r R (fun i => if i = 1 then w else z 0)) (z 1) := by
  have h_rep := bochner_F_limit_slice1_cauchy_rep r R hr hR f h_holo_eps h_slice1_lim_comm
  exact differentiable_slice1_of_cauchy_representation (TubeDomain (LShapeConvexHull r R))
    (bochner_F_limit f r R) h_rep z hz

lemma osgood_fin2 {U : Set (Fin 2 → ℂ)} (hU : IsOpen U)
    (f : (Fin 2 → ℂ) → ℂ) (h_cont : ContinuousOn f U)
    (h_diff0 : ∀ z ∈ U,
      DifferentiableAt ℂ (fun w => f (fun i => if i = 0 then w else z 1)) (z 0))
    (h_diff1 : ∀ z ∈ U,
      DifferentiableAt ℂ (fun w => f (fun i => if i = 1 then w else z 0)) (z 1))
    (z : Fin 2 → ℂ) (hz : z ∈ U) : DifferentiableAt ℂ f z := by
  let e := ContinuousLinearEquiv.finTwoArrow ℂ ℂ
  let U' : Set (ℂ × ℂ) := e.symm ⁻¹' U
  have hU' : IsOpen U' := hU.preimage e.symm.continuous
  let f' : ℂ × ℂ → ℂ := f ∘ e.symm
  have h_cont' : ContinuousOn f' U' :=
    h_cont.comp e.symm.continuous.continuousOn (fun _ hx => hx)
  have h_holo_x : ∀ (y : ℂ), DifferentiableOn ℂ (fun x => f' (x, y)) {x | (x, y) ∈ U'} := by
    intro y x hx
    have hx_U : (e.symm (x, y)) ∈ U := hx
    have hd := h_diff0 (e.symm (x, y)) hx_U
    have heq : (fun w => f' (w, y)) =
        (fun w => f (fun i => if i = 0 then w else (e.symm (x, y)) 1)) := by
      ext w
      change f (e.symm (w, y)) = f (fun i => if i = 0 then w else (e.symm (x, y)) 1)
      congr 1
      ext i
      fin_cases i <;> simp [e]
    rw [heq]
    have hz0 : (e.symm (x, y)) 0 = x := by simp [e]
    rw [← hz0]
    exact hd.differentiableWithinAt
  have h_holo_y : ∀ (x : ℂ), DifferentiableOn ℂ (fun y => f' (x, y)) {y | (x, y) ∈ U'} := by
    intro x y hy
    have hy_U : (e.symm (x, y)) ∈ U := hy
    have hd := h_diff1 (e.symm (x, y)) hy_U
    have heq : (fun w => f' (x, w)) =
        (fun w => f (fun i => if i = 1 then w else (e.symm (x, y)) 0)) := by
      ext w
      change f (e.symm (x, w)) = f (fun i => if i = 1 then w else (e.symm (x, y)) 0)
      congr 1
      ext i
      fin_cases i <;> simp [e]
    rw [heq]
    have hz1 : (e.symm (x, y)) 1 = y := by simp [e]
    rw [← hz1]
    exact hd.differentiableWithinAt
  have h_diff_f' : DifferentiableOn ℂ f' U' := Analysis.osgood_2d hU' f' h_cont' h_holo_x h_holo_y
  have hz_U' : e z ∈ U' := by
    simp only [U', mem_preimage, ContinuousLinearEquiv.symm_apply_apply, hz]
  have hd_at' : DifferentiableAt ℂ f' (e z) :=
    (h_diff_f' (e z) hz_U').differentiableAt (hU'.mem_nhds hz_U')
  have heq : f = f' ∘ e := by
    ext w
    change f w = f (e.symm (e w))
    rw [ContinuousLinearEquiv.symm_apply_apply]
  rw [heq]
  exact hd_at'.comp z e.differentiableAt

lemma bochner_F_limit_diffAt (r R : ℝ) (hr : 0 < r) (hR : r < R)
    (f : (Fin 2 → ℂ) → ℂ)
    (h_holo_eps : ∀ ε > 0,
      DifferentiableOn ℂ (bochner_F_eps f ε r R) (TubeDomain (LShapeConvexHull r R)))
    (h_cont : ContinuousOn (bochner_F_limit f r R) (TubeDomain (LShapeConvexHull r R)))
    (h_slice0_lim_comm : ∀ z ∈ TubeDomain (LShapeConvexHull r R), ∀ c : ℂ, ∀ ρ > 0,
      CircleIntegrable (fun ζ => bochner_F_limit f r R (fun i => if i = 0 then ζ else z 1)) c ρ ∧
      ∀ w ∈ Metric.ball c ρ,
        limUnder (𝓝[>] 0) (fun ε => (2 * ↑Real.pi * Complex.I : ℂ)⁻¹ • ∮ ζ in C(c, ρ),
          (ζ - w)⁻¹ • bochner_F_eps f ε r R (fun i => if i = 0 then ζ else z 1)) =
        (2 * π * I : ℂ)⁻¹ • ∮ ζ in C(c, ρ),
          (ζ - w)⁻¹ • bochner_F_limit f r R (fun i => if i = 0 then ζ else z 1))
    (h_slice1_lim_comm : ∀ z ∈ TubeDomain (LShapeConvexHull r R), ∀ c : ℂ, ∀ ρ > 0,
      CircleIntegrable (fun ζ => bochner_F_limit f r R (fun i => if i = 1 then ζ else z 0)) c ρ ∧
      ∀ w ∈ Metric.ball c ρ,
        limUnder (𝓝[>] 0) (fun ε => (2 * ↑Real.pi * Complex.I : ℂ)⁻¹ • ∮ ζ in C(c, ρ),
          (ζ - w)⁻¹ • bochner_F_eps f ε r R (fun i => if i = 1 then ζ else z 0)) =
        (2 * π * I : ℂ)⁻¹ • ∮ ζ in C(c, ρ),
          (ζ - w)⁻¹ • bochner_F_limit f r R (fun i => if i = 1 then ζ else z 0))
    (z : Fin 2 → ℂ) (hz : z ∈ TubeDomain (LShapeConvexHull r R)) :
    DifferentiableAt ℂ (bochner_F_limit f r R) z := by
  have h_diff0 : ∀ w ∈ TubeDomain (LShapeConvexHull r R),
      DifferentiableAt ℂ
        (fun ζ => bochner_F_limit f r R (fun i => if i = 0 then ζ else w 1)) (w 0) :=
    fun w hw => bochner_F_limit_slice0_diff r R hr hR f h_holo_eps h_slice0_lim_comm w hw
  have h_diff1 : ∀ w ∈ TubeDomain (LShapeConvexHull r R),
      DifferentiableAt ℂ
        (fun ζ => bochner_F_limit f r R (fun i => if i = 1 then ζ else w 0)) (w 1) :=
    fun w hw => bochner_F_limit_slice1_diff r R hr hR f h_holo_eps h_slice1_lim_comm w hw
  have hU_open : IsOpen (TubeDomain (LShapeConvexHull r R)) :=
    isOpen_TubeDomain (isOpen_LShapeConvexHull r R)
  exact osgood_fin2 hU_open (bochner_F_limit f r R) h_cont h_diff0 h_diff1 z hz

lemma bochner_F_limit_holo (r R : ℝ) (hr : 0 < r) (hR : r < R)
    (f : (Fin 2 → ℂ) → ℂ)
    (h_holo_eps : ∀ ε > 0,
      DifferentiableOn ℂ (bochner_F_eps f ε r R) (TubeDomain (LShapeConvexHull r R)))
    (h_cont : ContinuousOn (bochner_F_limit f r R) (TubeDomain (LShapeConvexHull r R)))
    (h_slice0_lim_comm : ∀ z ∈ TubeDomain (LShapeConvexHull r R), ∀ c : ℂ, ∀ ρ > 0,
      CircleIntegrable (fun ζ => bochner_F_limit f r R (fun i => if i = 0 then ζ else z 1)) c ρ ∧
      ∀ w ∈ Metric.ball c ρ,
        limUnder (𝓝[>] 0) (fun ε => (2 * ↑Real.pi * Complex.I : ℂ)⁻¹ • ∮ ζ in C(c, ρ),
          (ζ - w)⁻¹ • bochner_F_eps f ε r R (fun i => if i = 0 then ζ else z 1)) =
        (2 * π * I : ℂ)⁻¹ • ∮ ζ in C(c, ρ),
          (ζ - w)⁻¹ • bochner_F_limit f r R (fun i => if i = 0 then ζ else z 1))
    (h_slice1_lim_comm : ∀ z ∈ TubeDomain (LShapeConvexHull r R), ∀ c : ℂ, ∀ ρ > 0,
      CircleIntegrable (fun ζ => bochner_F_limit f r R (fun i => if i = 1 then ζ else z 0)) c ρ ∧
      ∀ w ∈ Metric.ball c ρ,
        limUnder (𝓝[>] 0) (fun ε => (2 * ↑Real.pi * Complex.I : ℂ)⁻¹ • ∮ ζ in C(c, ρ),
          (ζ - w)⁻¹ • bochner_F_eps f ε r R (fun i => if i = 1 then ζ else z 0)) =
        (2 * π * I : ℂ)⁻¹ • ∮ ζ in C(c, ρ),
          (ζ - w)⁻¹ • bochner_F_limit f r R (fun i => if i = 1 then ζ else z 0)) :
    DifferentiableOn ℂ (bochner_F_limit f r R) (TubeDomain (LShapeConvexHull r R)) := by
  apply differentiableOn_of_differentiableAt_all
  intro z hz
  exact bochner_F_limit_diffAt r R hr hR f h_holo_eps h_cont
    h_slice0_lim_comm h_slice1_lim_comm z hz

lemma bochner_limit_eps (r R : ℝ) (hr : 0 < r) (hR : r < R)
    (f : (Fin 2 → ℂ) → ℂ) (_hf_holo : DifferentiableOn ℂ f (TubeDomain (LShape r R)))
    (h_holo_eps : ∀ ε > 0,
      DifferentiableOn ℂ (bochner_F_eps f ε r R) (TubeDomain (LShapeConvexHull r R)))
    (h_cont : ContinuousOn (bochner_F_limit f r R) (TubeDomain (LShapeConvexHull r R)))
    (h_eq_eps : ∀ ε > 0,
      EqOn (bochner_F_eps f ε r R) (bochner_f_eps f ε) (TubeDomain (LShape r R)))
    (h_slice0_lim_comm : ∀ z ∈ TubeDomain (LShapeConvexHull r R), ∀ c : ℂ, ∀ ρ > 0,
      CircleIntegrable (fun ζ => bochner_F_limit f r R (fun i => if i = 0 then ζ else z 1)) c ρ ∧
      ∀ w ∈ Metric.ball c ρ,
        limUnder (𝓝[>] 0) (fun ε => (2 * ↑Real.pi * Complex.I : ℂ)⁻¹ • ∮ ζ in C(c, ρ),
          (ζ - w)⁻¹ • bochner_F_eps f ε r R (fun i => if i = 0 then ζ else z 1)) =
        (2 * π * I : ℂ)⁻¹ • ∮ ζ in C(c, ρ),
          (ζ - w)⁻¹ • bochner_F_limit f r R (fun i => if i = 0 then ζ else z 1))
    (h_slice1_lim_comm : ∀ z ∈ TubeDomain (LShapeConvexHull r R), ∀ c : ℂ, ∀ ρ > 0,
      CircleIntegrable (fun ζ => bochner_F_limit f r R (fun i => if i = 1 then ζ else z 0)) c ρ ∧
      ∀ w ∈ Metric.ball c ρ,
        limUnder (𝓝[>] 0) (fun ε => (2 * ↑Real.pi * Complex.I : ℂ)⁻¹ • ∮ ζ in C(c, ρ),
          (ζ - w)⁻¹ • bochner_F_eps f ε r R (fun i => if i = 1 then ζ else z 0)) =
        (2 * π * I : ℂ)⁻¹ • ∮ ζ in C(c, ρ),
          (ζ - w)⁻¹ • bochner_F_limit f r R (fun i => if i = 1 then ζ else z 0)) :
    ∃ (F : (Fin 2 → ℂ) → ℂ),
      DifferentiableOn ℂ F (TubeDomain (LShapeConvexHull r R)) ∧
      EqOn F f (TubeDomain (LShape r R)) := by
  use bochner_F_limit f r R
  constructor
  · exact bochner_F_limit_holo r R hr hR f h_holo_eps h_cont
      h_slice0_lim_comm h_slice1_lim_comm
  · exact bochner_F_limit_eq_on_tube r R f h_eq_eps

theorem bochner_tube_theorem (r R : ℝ) (hr : 0 < r) (hR : r < R)
    (f : (Fin 2 → ℂ) → ℂ)
    (hf_holo : DifferentiableOn ℂ f (TubeDomain (LShape r R)))
    (hf_bound : ∃ M : ℝ, ∀ z : Fin 2 → ℂ, ‖f z‖ ≤ M)
    (h_cont : ContinuousOn (bochner_F_limit f r R) (TubeDomain (LShapeConvexHull r R)))
    (h_slice0_lim_comm : ∀ z ∈ TubeDomain (LShapeConvexHull r R), ∀ c : ℂ, ∀ ρ > 0,
      CircleIntegrable (fun ζ => bochner_F_limit f r R (fun i => if i = 0 then ζ else z 1)) c ρ ∧
      ∀ w ∈ Metric.ball c ρ,
        limUnder (𝓝[>] 0) (fun ε => (2 * ↑Real.pi * Complex.I : ℂ)⁻¹ • ∮ ζ in C(c, ρ),
          (ζ - w)⁻¹ • bochner_F_eps f ε r R (fun i => if i = 0 then ζ else z 1)) =
        (2 * π * I : ℂ)⁻¹ • ∮ ζ in C(c, ρ),
          (ζ - w)⁻¹ • bochner_F_limit f r R (fun i => if i = 0 then ζ else z 1))
    (h_slice1_lim_comm : ∀ z ∈ TubeDomain (LShapeConvexHull r R), ∀ c : ℂ, ∀ ρ > 0,
      CircleIntegrable (fun ζ => bochner_F_limit f r R (fun i => if i = 1 then ζ else z 0)) c ρ ∧
      ∀ w ∈ Metric.ball c ρ,
        limUnder (𝓝[>] 0) (fun ε => (2 * ↑Real.pi * Complex.I : ℂ)⁻¹ • ∮ ζ in C(c, ρ),
          (ζ - w)⁻¹ • bochner_F_eps f ε r R (fun i => if i = 1 then ζ else z 0)) =
        (2 * π * I : ℂ)⁻¹ • ∮ ζ in C(c, ρ),
          (ζ - w)⁻¹ • bochner_F_limit f r R (fun i => if i = 1 then ζ else z 0)) :
    ∃ (F : (Fin 2 → ℂ) → ℂ),
      DifferentiableOn ℂ F (TubeDomain (LShapeConvexHull r R)) ∧
      EqOn F f (TubeDomain (LShape r R)) := by
  have h_holo_eps : ∀ ε > 0,
      DifferentiableOn ℂ (bochner_F_eps f ε r R) (TubeDomain (LShapeConvexHull r R)) :=
    fun ε hε => bochner_F_eps_holo r R hr hR f hf_holo hf_bound ε hε
  have h_eq_eps : ∀ ε > 0,
      EqOn (bochner_F_eps f ε r R) (bochner_f_eps f ε) (TubeDomain (LShape r R)) :=
    fun ε hε => bochner_F_eps_eq_f r R hr hR f hf_holo hf_bound ε hε
  exact bochner_limit_eps r R hr hR f hf_holo h_holo_eps h_cont h_eq_eps
    h_slice0_lim_comm h_slice1_lim_comm
end Bochner

lemma isOpen_TubeDomain_minus (V_plus : Set (Fin n → ℝ)) (hV_open : IsOpen V_plus) :
    IsOpen (TubeDomain ((fun v : Fin n → ℝ => -v) '' V_plus)) := by
  have h_img : ((fun v => -v) '' V_plus) = (fun v => -v) ⁻¹' V_plus := by
    ext v
    simp
  rw [h_img]
  have h_minus_open : IsOpen ((fun v => -v) ⁻¹' V_plus) := hV_open.preimage continuous_neg
  exact isOpen_TubeDomain h_minus_open

lemma isOpen_wedge_neighborhood (V_plus U : Set (Fin n → ℝ)) (hV_open : IsOpen V_plus)
    (r : (Fin n → ℝ) → ℝ) :
    IsOpen (TubeDomain V_plus ∪ TubeDomain ((fun v : Fin n → ℝ => -v) '' V_plus) ∪
    ⋃ x ∈ U, Metric.ball (fun i => (x i : ℂ)) (r x)) := by
  apply IsOpen.union
  · exact (isOpen_TubeDomain hV_open).union (isOpen_TubeDomain_minus V_plus hV_open)
  · exact isOpen_biUnion (fun x _ => Metric.isOpen_ball)

lemma wedge_subset_union_balls (V_plus U : Set (Fin n → ℝ))
    (r : (Fin n → ℝ) → ℝ) (hr : ∀ x ∈ U, 0 < r x) :
    WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U ⊆
    TubeDomain V_plus ∪ TubeDomain ((fun v : Fin n → ℝ => -v) '' V_plus) ∪
    ⋃ x ∈ U, Metric.ball (fun i => (x i : ℂ)) (r x) := by
  intro z hz
  rcases hz with (hz_plus | hz_minus) | hz_edge
  · left; left; exact hz_plus
  · left; right; exact hz_minus
  · right
    rcases hz_edge with ⟨hx_U, hx_im⟩
    let x : Fin n → ℝ := fun i => (z i).re
    have hx_eq : (fun i => (x i : ℂ)) = z := by
      ext i
      have h_im : (z i).im = 0 := congr_fun hx_im i
      exact Complex.ext rfl (by simp [x, h_im])
    simp only [mem_iUnion]
    refine ⟨x, hx_U, ?_⟩
    rw [hx_eq]
    exact Metric.mem_ball_self (hr x hx_U)

lemma dist_real_le_dist {n : ℕ} (z : Fin n → ℂ) (x : Fin n → ℝ) :
    dist (fun i => (((z i).re : ℝ) : ℂ)) (fun i => (x i : ℂ)) ≤ dist z (fun i => (x i : ℂ)) := by
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro i
  have h_le : dist (((z i).re : ℝ) : ℂ) (x i : ℂ) ≤ dist (z i) (x i : ℂ) := by
    rw [dist_eq_norm, dist_eq_norm]
    have heq : (((z i).re : ℝ) : ℂ) - (x i : ℂ) = (((z i - (x i : ℂ)).re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
    rw [heq, Complex.norm_real]
    exact Complex.abs_re_le_norm (z i - (x i : ℂ))
  exact h_le.trans (dist_le_pi_dist z (fun i => (x i : ℂ)) i)

lemma real_point_in_ball_inter {n : ℕ} {x y : Fin n → ℝ} {rx ry : ℝ}
    {z : Fin n → ℂ} (hzx : z ∈ Metric.ball (fun i => (x i : ℂ)) rx)
    (hzy : z ∈ Metric.ball (fun i => (y i : ℂ)) ry) :
    (fun i => (((z i).re : ℝ) : ℂ)) ∈ Metric.ball (fun i => (x i : ℂ)) rx ∧
    (fun i => (((z i).re : ℝ) : ℂ)) ∈ Metric.ball (fun i => (y i : ℂ)) ry := by
  constructor
  · have h := Metric.mem_ball.mp hzx
    exact Metric.mem_ball.mpr (lt_of_le_of_lt (dist_real_le_dist z x) h)
  · have h := Metric.mem_ball.mp hzy
    exact Metric.mem_ball.mpr (lt_of_le_of_lt (dist_real_le_dist z y) h)

noncomputable def ofRealPi (n : ℕ) : (Fin n → ℝ) →L[ℝ] (Fin n → ℂ) :=
  ContinuousLinearMap.pi (fun i => Complex.ofRealCLM.comp (ContinuousLinearMap.proj i))

lemma ofRealPi_apply {n : ℕ} (x : Fin n → ℝ) : ofRealPi n x = (fun i => (x i : ℂ)) := by
  ext i
  simp [ofRealPi]

lemma dist_ofReal_eq_dist {n : ℕ} (x y : Fin n → ℝ) :
    dist (fun i => (x i : ℂ)) (fun i => (y i : ℂ)) = dist x y := by
  apply le_antisymm
  · apply (dist_pi_le_iff dist_nonneg).mpr
    intro i
    have heq : dist (x i : ℂ) (y i : ℂ) = dist (x i) (y i) := by
      rw [dist_eq_norm, dist_eq_norm]
      have hsub : (x i : ℂ) - (y i : ℂ) = ((x i - y i : ℝ) : ℂ) := by
        apply Complex.ext <;> simp
      rw [hsub, Complex.norm_real]
    rw [heq]
    exact dist_le_pi_dist x y i
  · apply (dist_pi_le_iff dist_nonneg).mpr
    intro i
    have heq : dist (x i : ℂ) (y i : ℂ) = dist (x i) (y i) := by
      rw [dist_eq_norm, dist_eq_norm]
      have hsub : (x i : ℂ) - (y i : ℂ) = ((x i - y i : ℝ) : ℂ) := by
        apply Complex.ext <;> simp
      rw [hsub, Complex.norm_real]
    rw [← heq]
    exact dist_le_pi_dist (fun j => (x j : ℂ)) (fun j => (y j : ℂ)) i

lemma mem_wedgeDomain_of_real {n : ℕ} {V_plus V_minus U : Set (Fin n → ℝ)}
    {t : Fin n → ℝ} (ht_U : t ∈ U) :
    (fun i => (t i : ℂ)) ∈ WedgeDomain V_plus V_minus U := by
  right
  simp only [mem_setOf_eq]
  refine ⟨?_, ?_⟩
  · have heq : (fun i => ((t i : ℂ).re)) = t := by
      ext i; simp
    rw [heq]
    exact ht_U
  · ext i
    simp

def HasLocalExtensionAt (V_plus U : Set (Fin n → ℝ))
    (f : (Fin n → ℂ) → ℂ) (x : Fin n → ℝ) (r_x : ℝ) (F_x : (Fin n → ℂ) → ℂ) : Prop :=
  0 < r_x ∧
  Metric.ball x r_x ⊆ U ∧
  AnalyticOnNhd ℂ F_x (Metric.ball (fun i => (x i : ℂ)) r_x) ∧
  EqOn F_x f (Metric.ball (fun i => (x i : ℂ)) r_x ∩
    WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U)

lemma isConnected_ball_inter {n : ℕ} (c1 c2 : Fin n → ℂ) (r1 r2 : ℝ)
    (h_ne : (Metric.ball c1 r1 ∩ Metric.ball c2 r2).Nonempty) :
    IsConnected (Metric.ball c1 r1 ∩ Metric.ball c2 r2) := by
  have h_conv : Convex ℝ (Metric.ball c1 r1 ∩ Metric.ball c2 r2) :=
    (convex_ball c1 r1).inter (convex_ball c2 r2)
  exact h_conv.isConnected h_ne

lemma eow_local_compat (V_plus U : Set (Fin n → ℝ))
    (f : (Fin n → ℂ) → ℂ)
    (x y : U) (rx ry : ℝ) (Fx Fy : (Fin n → ℂ) → ℂ)
    (hx_ext : HasLocalExtensionAt V_plus U f x.1 rx Fx)
    (hy_ext : HasLocalExtensionAt V_plus U f y.1 ry Fy) :
    EqOn Fx Fy (Metric.ball (fun i => (x.1 i : ℂ)) rx ∩ Metric.ball (fun i => (y.1 i : ℂ)) ry) := by
  let cx : Fin n → ℂ := fun i => (x.1 i : ℂ)
  let cy : Fin n → ℂ := fun i => (y.1 i : ℂ)
  let W : Set (Fin n → ℂ) := Metric.ball cx rx ∩ Metric.ball cy ry
  by_cases h_inter : W.Nonempty
  · rcases h_inter with ⟨z, hzx, hzy⟩
    have ⟨hzx_re, hzy_re⟩ := real_point_in_ball_inter hzx hzy
    let a : Fin n → ℝ := fun i => (z i).re
    have ha_cx : (fun i => (a i : ℂ)) ∈ Metric.ball cx rx := hzx_re
    have ha_cy : (fun i => (a i : ℂ)) ∈ Metric.ball cy ry := hzy_re
    have ha_W : ofRealPi n a ∈ W := by
      rw [ofRealPi_apply]
      exact ⟨ha_cx, ha_cy⟩
    have ha_ball_x : a ∈ Metric.ball x.1 rx := by
      rw [Metric.mem_ball] at ha_cx ⊢
      rw [← dist_ofReal_eq_dist]
      exact ha_cx
    have ha_ball_y : a ∈ Metric.ball y.1 ry := by
      rw [Metric.mem_ball] at ha_cy ⊢
      rw [← dist_ofReal_eq_dist]
      exact ha_cy
    have hW_open : IsOpen W := (Metric.isOpen_ball).inter Metric.isOpen_ball
    have hW_conn : IsConnected W := isConnected_ball_inter cx cy rx ry ⟨z, hzx, hzy⟩
    have hf_ana : AnalyticOnNhd ℂ Fx W := hx_ext.2.2.1.mono inter_subset_left
    have hg_ana : AnalyticOnNhd ℂ Fy W := hy_ext.2.2.1.mono inter_subset_right
    have h_real_nhds : ∀ᶠ t : Fin n → ℝ in 𝓝 a, Fx (ofRealPi n t) = Fy (ofRealPi n t) := by
      have h_open_ball_inter : IsOpen (Metric.ball x.1 rx ∩ Metric.ball y.1 ry) :=
        Metric.isOpen_ball.inter Metric.isOpen_ball
      have ha_in_inter : a ∈ Metric.ball x.1 rx ∩ Metric.ball y.1 ry := ⟨ha_ball_x, ha_ball_y⟩
      have h_mem_nhds : Metric.ball x.1 rx ∩ Metric.ball y.1 ry ∈ 𝓝 a :=
        h_open_ball_inter.mem_nhds ha_in_inter
      filter_upwards [h_mem_nhds] with t ht
      rw [ofRealPi_apply]
      have ht_ball_x : (fun i => (t i : ℂ)) ∈ Metric.ball cx rx := by
        rw [Metric.mem_ball]
        rw [dist_ofReal_eq_dist]
        exact ht.1
      have ht_ball_y : (fun i => (t i : ℂ)) ∈ Metric.ball cy ry := by
        rw [Metric.mem_ball]
        rw [dist_ofReal_eq_dist]
        exact ht.2
      have ht_U : t ∈ U := hx_ext.2.1 ht.1
      have ht_wedge : (fun i => (t i : ℂ)) ∈
          WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U :=
        mem_wedgeDomain_of_real ht_U
      have h_eq_x := hx_ext.2.2.2 ⟨ht_ball_x, ht_wedge⟩
      have h_eq_y := hy_ext.2.2.2 ⟨ht_ball_y, ht_wedge⟩
      rw [h_eq_x, h_eq_y]
    exact Analysis.analytic_eq_of_real_eq_R_N hW_open hW_conn Fx Fy hf_ana hg_ana
      a (ofRealPi n) ofRealPi_apply ha_W h_real_nhds
  · intro w hw
    exfalso
    exact h_inter ⟨w, hw⟩

lemma local_extension_assembly (V_plus U : Set (Fin n → ℝ))
    (f : (Fin n → ℂ) → ℂ)
    (h_exists : ∀ x ∈ U, ∃ r_x > 0, Metric.ball x r_x ⊆ U ∧ ∃ F_x : (Fin n → ℂ) → ℂ,
      AnalyticOnNhd ℂ F_x (Metric.ball (fun i => (x i : ℂ)) r_x) ∧
      EqOn F_x f (Metric.ball (fun i => (x i : ℂ)) r_x ∩
        WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U))
    (h_compat : ∀ (x y : U) (rx ry : ℝ) (Fx Fy : (Fin n → ℂ) → ℂ),
      HasLocalExtensionAt V_plus U f x.1 rx Fx →
      HasLocalExtensionAt V_plus U f y.1 ry Fy →
      EqOn Fx Fy (Metric.ball (fun i => (x.1 i : ℂ)) rx ∩ Metric.ball (fun i => (y.1 i : ℂ)) ry)) :
    ∃ (r : (Fin n → ℝ) → ℝ) (_hr : ∀ x ∈ U, 0 < r x) (F_loc : (Fin n → ℝ) → (Fin n → ℂ) → ℂ),
      (∀ x ∈ U, DifferentiableOn ℂ (F_loc x) (Metric.ball (fun i => (x i : ℂ)) (r x))) ∧
      (∀ x ∈ U, EqOn (F_loc x) f (Metric.ball (fun i => (x i : ℂ)) (r x) ∩
        WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U)) ∧
      (∀ (x y : U), EqOn (F_loc x.1) (F_loc y.1)
        (Metric.ball (fun i => (x.1 i : ℂ)) (r x.1) ∩
          Metric.ball (fun i => (y.1 i : ℂ)) (r y.1))) := by
  choose! r_x hr_x h_sub F_x hF_x using h_exists
  refine ⟨r_x, hr_x, F_x, ?_, ?_, ?_⟩
  · intro x hx
    exact (hF_x x hx).1.differentiableOn
  · intro x hx
    exact (hF_x x hx).2
  · intro x y
    have hx_ext : HasLocalExtensionAt V_plus U f x.1 (r_x x.1) (F_x x.1) :=
      ⟨hr_x x.1 x.2, h_sub x.1 x.2, (hF_x x.1 x.2).1, (hF_x x.1 x.2).2⟩
    have hy_ext : HasLocalExtensionAt V_plus U f y.1 (r_x y.1) (F_x y.1) :=
      ⟨hr_x y.1 y.2, h_sub y.1 y.2, (hF_x y.1 y.2).1, (hF_x y.1 y.2).2⟩
    exact h_compat x y (r_x x.1) (r_x y.1) (F_x x.1) (F_x y.1) hx_ext hy_ext

lemma analyticOnNhd_ball_of_analyticAt {n : ℕ} {f : (Fin n → ℂ) → ℂ} {x : Fin n → ℂ}
    (h : AnalyticAt ℂ f x) :
    ∃ r > 0, AnalyticOnNhd ℂ f (Metric.ball x r) := by
  have h_open : IsOpen {y | AnalyticAt ℂ f y} := isOpen_analyticAt ℂ f
  have h_in : x ∈ {y | AnalyticAt ℂ f y} := h
  rcases Metric.isOpen_iff.mp h_open x h_in with ⟨r, hr_pos, hr_sub⟩
  exact ⟨r, hr_pos, fun y hy => hr_sub hy⟩

lemma exists_ball_subset_and_analyticOnNhd {n : ℕ} {f : (Fin n → ℂ) → ℂ} {x : Fin n → ℝ}
    {U : Set (Fin n → ℝ)} (hU : IsOpen U) (hx_U : x ∈ U)
    (h_ana : AnalyticAt ℂ f (fun i => (x i : ℂ))) :
    ∃ r > 0, Metric.ball x r ⊆ U ∧
      AnalyticOnNhd ℂ f (Metric.ball (fun i => (x i : ℂ)) r) := by
  rcases Metric.isOpen_iff.mp hU x hx_U with ⟨r1, hr1_pos, hr1_sub⟩
  rcases analyticOnNhd_ball_of_analyticAt h_ana with ⟨r2, hr2_pos, hr2_ana⟩
  let r := min r1 r2
  have hr_pos : 0 < r := lt_min hr1_pos hr2_pos
  refine ⟨r, hr_pos, ?_, ?_⟩
  · exact (Metric.ball_subset_ball (min_le_left r1 r2)).trans hr1_sub
  · exact hr2_ana.mono (Metric.ball_subset_ball (min_le_right r1 r2))

lemma analyticAt_cauchy_integral {f : ℂ → ℂ} {c : ℂ} {R : NNReal} (hR : 0 < R)
    (hf : CircleIntegrable f c R) :
    AnalyticAt ℂ (fun w => (2 * ↑Real.pi * I : ℂ)⁻¹ • ∮ z in C(c, R), (z - w)⁻¹ • f z) c := by
  have h_series := hasFPowerSeriesOn_cauchy_integral hf hR
  have hc_mem : c ∈ Metric.eball c R := by
    rw [Metric.eball_coe]
    exact Metric.mem_ball_self hR
  exact h_series.analyticAt_of_mem hc_mem

lemma analyticAt_comp_clm {n : ℕ} (g : ℂ → ℂ) (L : (Fin n → ℂ) →L[ℂ] ℂ) (x : Fin n → ℂ)
    (hg : AnalyticAt ℂ g (L x)) :
    AnalyticAt ℂ (g ∘ L) x :=
  hg.comp (L.analyticAt x)

lemma exists_ne_zero_of_open_cone_1d (V : Set (Fin 1 → ℝ)) (hV : IsOpen V)
    (_hV_cone : ∀ v ∈ V, ∀ (c : ℝ), c > 0 → (fun i => c * v i) ∈ V)
    (hV_ne : V.Nonempty) : ∃ v ∈ V, v 0 ≠ 0 := by
  rcases hV_ne with ⟨v, hv⟩
  by_cases h0 : v 0 = 0
  · have hveq : v = 0 := by ext i; fin_cases i; exact h0
    rw [hveq] at hv
    rcases Metric.isOpen_iff.mp hV 0 hv with ⟨ε, hε_pos, hε_sub⟩
    let v' : Fin 1 → ℝ := fun _ => ε / 2
    have hv'_mem : v' ∈ Metric.ball (0 : Fin 1 → ℝ) ε := by
      rw [Metric.mem_ball]
      apply (dist_pi_lt_iff hε_pos).mpr
      intro i
      fin_cases i
      dsimp [v']
      rw [dist_zero_right, Real.norm_eq_abs, abs_of_pos (half_pos hε_pos)]
      exact half_lt_self hε_pos
    have hv' : v' ∈ V := hε_sub hv'_mem
    have hv'0 : v' 0 ≠ 0 := (half_pos hε_pos).ne'
    exact ⟨v', hv', hv'0⟩
  · exact ⟨v, hv, h0⟩

lemma slice_fun_eq_f_1d (f : (Fin 1 → ℂ) → ℂ) (x : Fin 1 → ℝ) (v : Fin 1 → ℝ)
    (hv0 : v 0 ≠ 0) (z : Fin 1 → ℂ) :
    slice_fun f (fun i => (x i : ℂ)) v ((z 0 - (x 0 : ℂ)) / (v 0 : ℂ)) = f z := by
  dsimp [slice_fun]
  have heq : (fun i : Fin 1 => (x i : ℂ) + ((z 0 - (x 0 : ℂ)) / (v 0 : ℂ)) * (v i : ℂ)) = z := by
    ext i
    fin_cases i
    dsimp
    have hv : (v 0 : ℂ) ≠ 0 := by exact_mod_cast hv0
    calc (x 0 : ℂ) + ((z 0 - (x 0 : ℂ)) / (v 0 : ℂ)) * (v 0 : ℂ)
      _ = (x 0 : ℂ) + (z 0 - (x 0 : ℂ)) := by rw [div_mul_cancel₀ _ hv]
      _ = z 0 := by ring
  rw [heq]

lemma exists_local_analytic_extension_cauchy_1d (V_plus U : Set (Fin 1 → ℝ))
    (hV_plus_open : IsOpen V_plus)
    (hV_plus_cone : ∀ v ∈ V_plus, ∀ (c : ℝ), c > 0 → (fun i => c * v i) ∈ V_plus)
    (hV_plus_ne : V_plus.Nonempty)
    (hU_open : IsOpen U)
    (f : (Fin 1 → ℂ) → ℂ)
    (h_cont : ContinuousOn f (WedgeDomain V_plus ((fun v : Fin 1 → ℝ => -v) '' V_plus) U))
    (h_holo_plus : DifferentiableOn ℂ f (TubeDomain V_plus))
    (h_holo_minus : DifferentiableOn ℂ f (TubeDomain ((fun v : Fin 1 → ℝ => -v) '' V_plus)))
    (x : Fin 1 → ℝ) (hx_U : x ∈ U) (r : ℝ) (_hr : 0 < r)
    (_h_ball_U : Metric.ball x r ⊆ U) :
    ∃ F_x : (Fin 1 → ℂ) → ℂ,
      AnalyticAt ℂ F_x (fun i => (x i : ℂ)) ∧
      EqOn F_x f (Metric.ball (fun i => (x i : ℂ)) r ∩
        WedgeDomain V_plus ((fun v : Fin 1 → ℝ => -v) '' V_plus) U) := by
  rcases exists_ne_zero_of_open_cone_1d V_plus hV_plus_open hV_plus_cone hV_plus_ne with
    ⟨v, hv, hv0⟩
  have h_slice := slice_analytic_at_zero V_plus U hV_plus_open hV_plus_cone hU_open f h_cont
    h_holo_plus h_holo_minus x hx_U v hv
  let g : ℂ → ℂ := slice_fun f (fun i => (x i : ℂ)) v
  let L : (Fin 1 → ℂ) → ℂ := fun z => (z 0 - (x 0 : ℂ)) / (v 0 : ℂ)
  have hL_ana : AnalyticAt ℂ L (fun i => (x i : ℂ)) := by
    dsimp [L]
    apply AnalyticAt.div_const
    apply AnalyticAt.sub
    · exact (ContinuousLinearMap.proj (R := ℂ) (0 : Fin 1)).analyticAt (fun i => (x i : ℂ))
    · exact analyticAt_const
  have hL_x : L (fun i => (x i : ℂ)) = 0 := by
    dsimp [L]
    simp
  let F_x : (Fin 1 → ℂ) → ℂ := g ∘ L
  have hF_ana : AnalyticAt ℂ F_x (fun i => (x i : ℂ)) := by
    rw [← hL_x] at h_slice
    exact h_slice.comp hL_ana
  use F_x
  refine ⟨hF_ana, ?_⟩
  intro z _hz
  dsimp [F_x, g, L]
  exact slice_fun_eq_f_1d f x v hv0 z

def LocalEOWCore {n : ℕ} (V_plus : Set (Fin n → ℝ)) (f : (Fin n → ℂ) → ℂ) (x : Fin n → ℝ) : Prop :=
  ∃ ρ : ℝ, 0 < ρ ∧ ∃ F : (Fin n → ℂ) → ℂ,
    AnalyticOnNhd ℂ F (Metric.ball (fun i => (x i : ℂ)) ρ) ∧
    (∃ W : Set (Fin n → ℂ), IsOpen W ∧ W.Nonempty ∧
      W ⊆ Metric.ball (fun i => (x i : ℂ)) ρ ∩ TubeDomain V_plus ∧ EqOn F f W) ∧
    (∃ W : Set (Fin n → ℂ), IsOpen W ∧ W.Nonempty ∧
      W ⊆ Metric.ball (fun i => (x i : ℂ)) ρ ∩
        TubeDomain ((fun v : Fin n → ℝ => -v) '' V_plus) ∧ EqOn F f W)

lemma eqOn_zero_of_convex_differentiableOn {n : ℕ} {S W : Set (Fin n → ℂ)}
    (hS_open : IsOpen S) (hS_conv : Convex ℝ S)
    {g : (Fin n → ℂ) → ℂ} (hg : DifferentiableOn ℂ g S)
    (hW_open : IsOpen W) (hWS : W ⊆ S) (hW_ne : W.Nonempty)
    (hgW : EqOn g 0 W) : EqOn g 0 S := by
  obtain ⟨w, hw⟩ := hW_ne
  intro p hp
  let φ : ℂ → (Fin n → ℂ) := fun t => w + t • (p - w)
  have hφ_diff : Differentiable ℂ φ := by
    unfold φ
    fun_prop
  have hφ_cont : Continuous φ := hφ_diff.continuous
  have hφ0 : φ 0 = w := by simp [φ]
  have hφ1 : φ 1 = p := by simp [φ]
  let T : Set ℂ := φ ⁻¹' S
  have hT_open : IsOpen T := hS_open.preimage hφ_cont
  have hT_conv : Convex ℝ T := by
    intro t₁ ht₁ t₂ ht₂ a b ha hb hab
    have hab' : (a : ℂ) + (b : ℂ) = 1 := by exact_mod_cast hab
    have h : φ (a • t₁ + b • t₂) = a • φ t₁ + b • φ t₂ := by
      ext i
      simp only [φ, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Complex.real_smul, smul_eq_mul]
      linear_combination (-(w i)) * hab'
    change φ (a • t₁ + b • t₂) ∈ S
    rw [h]
    exact hS_conv ht₁ ht₂ ha hb hab
  have h_an : AnalyticOnNhd ℂ (g ∘ φ) T :=
    (hg.comp hφ_diff.differentiableOn (fun t ht => ht)).analyticOnNhd hT_open
  have h0T : (0 : ℂ) ∈ T := by
    change φ 0 ∈ S
    rw [hφ0]
    exact hWS hw
  have h1T : (1 : ℂ) ∈ T := by
    change φ 1 ∈ S
    rw [hφ1]
    exact hp
  have h_ev : (g ∘ φ) =ᶠ[nhds (0 : ℂ)] 0 := by
    have hWn : W ∈ nhds (φ 0) := by
      rw [hφ0]
      exact hW_open.mem_nhds hw
    filter_upwards [hφ_cont.continuousAt.preimage_mem_nhds hWn] with t ht
    exact hgW ht
  have h_zero := h_an.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    hT_conv.isPreconnected h0T h_ev
  simpa [Function.comp, hφ1] using h_zero h1T

lemma exists_local_analytic_extension_of_core {n : ℕ} (V_plus U : Set (Fin n → ℝ))
    (hV_plus_open : IsOpen V_plus)
    (hV_plus_convex : Convex ℝ V_plus)
    (hV_plus_cone : ∀ v ∈ V_plus, ∀ (c : ℝ), c > 0 → (fun i => c * v i) ∈ V_plus)
    (f : (Fin n → ℂ) → ℂ)
    (h_cont : ContinuousOn f (WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U))
    (h_holo_plus : DifferentiableOn ℂ f (TubeDomain V_plus))
    (h_holo_minus : DifferentiableOn ℂ f (TubeDomain ((fun v : Fin n → ℝ => -v) '' V_plus)))
    (x : Fin n → ℝ) (h_core : LocalEOWCore V_plus f x) :
    ∃ F_x : (Fin n → ℂ) → ℂ,
      AnalyticAt ℂ F_x (fun i => (x i : ℂ)) ∧
      EqOn F_x f (WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U) := by
  classical
  obtain ⟨ρ, hρ, F, hF_an, ⟨W₁, hW₁o, hW₁n, hW₁s, hW₁e⟩, ⟨W₂, hW₂o, hW₂n, hW₂s, hW₂e⟩⟩ := h_core
  have hF_diff : DifferentiableOn ℂ F (Metric.ball (fun i => (x i : ℂ)) ρ) :=
    hF_an.differentiableOn
  have hB_open : IsOpen (Metric.ball (fun i => (x i : ℂ)) ρ) := Metric.isOpen_ball
  have hB_conv : Convex ℝ (Metric.ball (fun i => (x i : ℂ)) ρ) := convex_ball _ _
  have hVm_conv : Convex ℝ ((fun v : Fin n → ℝ => -v) '' V_plus) := by
    rintro _ ⟨v₁, hv₁, rfl⟩ _ ⟨v₂, hv₂, rfl⟩ a b ha hb hab
    exact ⟨a • v₁ + b • v₂, hV_plus_convex hv₁ hv₂ ha hb hab, by simp [add_comm]⟩
  have h_eq₁ : EqOn F f (Metric.ball (fun i => (x i : ℂ)) ρ ∩ TubeDomain V_plus) := by
    have hS_open : IsOpen (Metric.ball (fun i => (x i : ℂ)) ρ ∩ TubeDomain V_plus) :=
      hB_open.inter (isOpen_TubeDomain hV_plus_open)
    have hS_conv : Convex ℝ (Metric.ball (fun i => (x i : ℂ)) ρ ∩ TubeDomain V_plus) :=
      hB_conv.inter (convex_TubeDomain hV_plus_convex)
    have hd : DifferentiableOn ℂ (F - f)
        (Metric.ball (fun i => (x i : ℂ)) ρ ∩ TubeDomain V_plus) :=
      (hF_diff.mono Set.inter_subset_left).sub (h_holo_plus.mono Set.inter_subset_right)
    have h0 := eqOn_zero_of_convex_differentiableOn hS_open hS_conv hd hW₁o hW₁s hW₁n
      (fun z hz => by simp [hW₁e hz])
    intro z hz
    simpa [sub_eq_zero] using h0 hz
  have h_eq₂ : EqOn F f (Metric.ball (fun i => (x i : ℂ)) ρ ∩
      TubeDomain ((fun v : Fin n → ℝ => -v) '' V_plus)) := by
    have hS_open : IsOpen (Metric.ball (fun i => (x i : ℂ)) ρ ∩
        TubeDomain ((fun v : Fin n → ℝ => -v) '' V_plus)) :=
      hB_open.inter (isOpen_TubeDomain_minus V_plus hV_plus_open)
    have hS_conv : Convex ℝ (Metric.ball (fun i => (x i : ℂ)) ρ ∩
        TubeDomain ((fun v : Fin n → ℝ => -v) '' V_plus)) :=
      hB_conv.inter (convex_TubeDomain hVm_conv)
    have hd : DifferentiableOn ℂ (F - f) (Metric.ball (fun i => (x i : ℂ)) ρ ∩
        TubeDomain ((fun v : Fin n → ℝ => -v) '' V_plus)) :=
      (hF_diff.mono Set.inter_subset_left).sub (h_holo_minus.mono Set.inter_subset_right)
    have h0 := eqOn_zero_of_convex_differentiableOn hS_open hS_conv hd hW₂o hW₂s hW₂n
      (fun z hz => by simp [hW₂e hz])
    intro z hz
    simpa [sub_eq_zero] using h0 hz
  obtain ⟨w₀, hw₀⟩ := hW₁n
  let v₀ : Fin n → ℝ := fun i => (w₀ i).im
  have hv₀ : v₀ ∈ V_plus := (hW₁s hw₀).2
  have h_real : ∀ z ∈ Metric.ball (fun i => (x i : ℂ)) ρ,
      z ∈ WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U → F z = f z := by
    intro z hzB hzW
    rcases hzW with (hzT | hzT) | ⟨hz_re, hz_im⟩
    · exact h_eq₁ ⟨hzB, hzT⟩
    · exact h_eq₂ ⟨hzB, hzT⟩
    · let zt : ℝ → (Fin n → ℂ) := fun t i => z i + (t : ℂ) * Complex.I * (v₀ i : ℂ)
      have hzt_cont : Continuous zt := by
        unfold zt
        fun_prop
      have hzt0 : zt 0 = z := by
        ext i
        simp [zt]
      have hzt_tend : Filter.Tendsto zt (nhdsWithin 0 (Set.Ioi 0)) (nhds z) :=
        (hzt_cont.tendsto' 0 z hzt0).mono_left nhdsWithin_le_nhds
      have h_pos : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0), t ∈ Set.Ioi (0 : ℝ) :=
        self_mem_nhdsWithin
      have h_inB : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0),
          zt t ∈ Metric.ball (fun i => (x i : ℂ)) ρ :=
        hzt_tend.eventually (hB_open.mem_nhds hzB)
      have h_inT : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0), zt t ∈ TubeDomain V_plus := by
        filter_upwards [h_pos] with t ht
        have hzi : ∀ i, (z i).im = 0 := fun i => congr_fun hz_im i
        have him : (fun i => (zt t i).im) = fun i => t * v₀ i := by
          ext i
          simp [zt, Complex.mul_im, hzi i]
        change (fun i => (zt t i).im) ∈ V_plus
        rw [him]
        exact hV_plus_cone v₀ hv₀ t ht
      have h_ev : (fun t => F (zt t)) =ᶠ[nhdsWithin 0 (Set.Ioi 0)] (fun t => f (zt t)) := by
        filter_upwards [h_inB, h_inT] with t htB htT
        exact h_eq₁ ⟨htB, htT⟩
      have hF_t : Filter.Tendsto (fun t => F (zt t)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (F z)) :=
        (hF_an z hzB).continuousAt.tendsto.comp hzt_tend
      have hz_wedge : z ∈ WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U :=
        Or.inr ⟨hz_re, hz_im⟩
      have hf_t : Filter.Tendsto (fun t => f (zt t)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (f z)) := by
        refine (h_cont z hz_wedge).tendsto.comp ?_
        refine tendsto_nhdsWithin_iff.mpr ⟨hzt_tend, ?_⟩
        filter_upwards [h_inT] with t htT
        exact Or.inl (Or.inl htT)
      exact tendsto_nhds_unique_of_eventuallyEq hF_t hf_t h_ev
  refine ⟨fun z => if z ∈ WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U
    then f z else F z, ?_, ?_⟩
  · have h_ev_eq : F =ᶠ[nhds (fun i => (x i : ℂ))] (fun z =>
        if z ∈ WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U then f z else F z) := by
      filter_upwards [hB_open.mem_nhds (Metric.mem_ball_self hρ)] with z hzB
      by_cases hzW : z ∈ WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U
      · rw [if_pos hzW]
        exact h_real z hzB hzW
      · rw [if_neg hzW]
    exact (hF_an _ (Metric.mem_ball_self hρ)).congr h_ev_eq
  · intro z hz
    dsimp
    rw [if_pos hz]

lemma exists_linearIndependent_mem_open {n : ℕ} {V : Set (Fin n → ℝ)} (hV : IsOpen V)
    (hne : V.Nonempty) :
    ∃ v : Fin n → (Fin n → ℝ), LinearIndependent ℝ v ∧ ∀ i, v i ∈ V := by
  obtain ⟨v₀, hv₀⟩ := hne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hV v₀ hv₀
  have h_basis : ∀ i : Fin n, (Pi.single i (1 : ℝ) : Fin n → ℝ) ∈ Submodule.span ℝ V := by
    intro i
    have h1 : v₀ + Pi.single i (ε / 2) ∈ V := by
      apply hball
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, Pi.norm_single, Real.norm_eq_abs,
        abs_of_pos (by positivity)]
      linarith
    have e : (Pi.single i (1 : ℝ) : Fin n → ℝ) =
        (ε / 2)⁻¹ • ((v₀ + Pi.single i (ε / 2)) - v₀) := by
      ext j
      by_cases h : j = i
      · subst h
        simp [hε.ne']
      · simp [h]
    rw [e]
    exact Submodule.smul_mem _ _
      (Submodule.sub_mem _ (Submodule.subset_span h1) (Submodule.subset_span hv₀))
  have h_span : Submodule.span ℝ V = ⊤ := by
    rw [eq_top_iff, ← (Pi.basisFun ℝ (Fin n)).span_eq]
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    simpa using h_basis i
  obtain ⟨b, hbV, hbspan, hbli⟩ := exists_linearIndependent ℝ V
  have hb_top : Submodule.span ℝ b = ⊤ := hbspan.trans h_span
  let B : Module.Basis b ℝ (Fin n → ℝ) :=
    Module.Basis.mk hbli (by rw [Subtype.range_coe, hb_top])
  haveI : Finite b := Module.Finite.finite_basis B
  letI : Fintype b := Fintype.ofFinite b
  have hcard : Fintype.card b = n := by
    have h := Module.finrank_eq_card_basis B
    simpa using h.symm
  let e : Fin n ≃ b := (Fintype.equivFinOfCardEq hcard).symm
  exact ⟨fun i => (e i : Fin n → ℝ), hbli.comp e e.injective, fun i => hbV (e i).2⟩

noncomputable def cAffine {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ)
    (w : Fin n → ℂ) : Fin n → ℂ :=
  fun i => (x i : ℂ) + Matrix.mulVec (M.map (algebraMap ℝ ℂ)) w i

lemma cAffine_im {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) (w : Fin n → ℂ) :
    (fun i => (cAffine M x w i).im) = Matrix.mulVec M (fun j => (w j).im) := by
  ext i
  simp [cAffine, Matrix.mulVec, dotProduct, Complex.im_sum, Complex.mul_im]

lemma cAffine_re {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) (w : Fin n → ℂ) :
    (fun i => (cAffine M x w i).re) = x + Matrix.mulVec M (fun j => (w j).re) := by
  ext i
  simp [cAffine, Matrix.mulVec, dotProduct, Complex.re_sum, Complex.mul_re]

lemma differentiable_cAffine {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    Differentiable ℂ (cAffine M x) := by
  unfold cAffine
  apply differentiable_pi.mpr
  intro i
  simp only [Matrix.mulVec, dotProduct]
  fun_prop

noncomputable def matrixMulVecCLM {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    (Fin n → ℂ) →L[ℂ] (Fin n → ℂ) :=
  ContinuousLinearMap.pi fun i => ∑ j, (A i j) • (ContinuousLinearMap.proj (R := ℂ) j)

lemma matrixMulVecCLM_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (z : Fin n → ℂ) :
    matrixMulVecCLM A z = Matrix.mulVec A z := by
  ext i
  simp [matrixMulVecCLM, Matrix.mulVec, dotProduct]

lemma exists_inverse_cAffine {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : IsUnit M)
    (x : Fin n → ℝ) :
    ∃ Ψ : (Fin n → ℂ) → (Fin n → ℂ), Differentiable ℂ Ψ ∧ (∀ z, AnalyticAt ℂ Ψ z) ∧
      (∀ z, cAffine M x (Ψ z) = z) ∧ (∀ w, Ψ (cAffine M x w) = w) := by
  have hdet : IsUnit M.det := (Matrix.isUnit_iff_isUnit_det M).mp hM
  have h1 : M.map (algebraMap ℝ ℂ) * (M⁻¹).map (algebraMap ℝ ℂ) = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv M hdet,
      Matrix.map_one _ (_root_.map_zero _) (_root_.map_one _)]
  have h2 : (M⁻¹).map (algebraMap ℝ ℂ) * M.map (algebraMap ℝ ℂ) = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul M hdet,
      Matrix.map_one _ (_root_.map_zero _) (_root_.map_one _)]
  let A := (M⁻¹).map (algebraMap ℝ ℂ)
  let xc : Fin n → ℂ := fun i => (x i : ℂ)
  refine ⟨fun z => Matrix.mulVec A (z - xc), ?_, ?_, ?_, ?_⟩
  · apply differentiable_pi.mpr
    intro i
    simp only [Matrix.mulVec, dotProduct]
    fun_prop
  · intro z
    have heq : (fun w => Matrix.mulVec A (w - xc)) = fun w => (matrixMulVecCLM A) (w - xc) := by
      ext w
      simp [matrixMulVecCLM_apply]
    rw [heq]
    have h := ((matrixMulVecCLM A).analyticAt (z - xc)).comp_sub xc
    rwa [sub_add_cancel] at h
  · intro z
    ext i
    have heq : cAffine M x (Matrix.mulVec A (z - xc)) i =
        (xc i) + Matrix.mulVec ((M.map (algebraMap ℝ ℂ)) * A) (z - xc) i := by
      simp [cAffine, Matrix.mulVec_mulVec, xc]
    rw [heq, h1, Matrix.one_mulVec]
    simp [xc]
  · intro w
    ext i
    have heq : (cAffine M x w - xc) = Matrix.mulVec (M.map (algebraMap ℝ ℂ)) w := by
      ext j
      simp [cAffine, xc]
    change (A.mulVec (cAffine M x w - xc)) i = w i
    rw [heq]
    have hmul : A.mulVec ((M.map (algebraMap ℝ ℂ)).mulVec w) =
        (A * M.map (algebraMap ℝ ℂ)).mulVec w := by
      simp [Matrix.mulVec_mulVec]
    rw [hmul, h2, Matrix.one_mulVec]

lemma isUnit_of_linearIndependent_cols {n : ℕ} (v : Fin n → (Fin n → ℝ))
    (hv : LinearIndependent ℝ v) : IsUnit (Matrix.of fun i j => v j i) := by
  rw [← Matrix.linearIndependent_cols_iff_isUnit]
  exact hv

lemma sum_pos_smul_mem_of_convex_cone {n : ℕ} (hn : 0 < n) {V : Set (Fin n → ℝ)}
    (hconv : Convex ℝ V)
    (hcone : ∀ v ∈ V, ∀ (c : ℝ), c > 0 → (fun i => c * v i) ∈ V)
    (v : Fin n → (Fin n → ℝ)) (hv : ∀ j, v j ∈ V) (y : Fin n → ℝ) (hy : ∀ j, 0 < y j) :
    ∑ j, y j • v j ∈ V := by
  have hs : 0 < ∑ j, y j :=
    Finset.sum_pos (fun j _ => hy j) ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  have hmem : ∑ j, (y j / ∑ k, y k) • v j ∈ V :=
    hconv.sum_mem (fun j _ => (div_pos (hy j) hs).le)
      (by rw [← Finset.sum_div, div_self hs.ne']) (fun j _ => hv j)
  have h := hcone _ hmem (∑ k, y k) hs
  convert h using 1
  ext i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  field_simp

lemma cAffine_mem_tube_plus {n : ℕ} (hn : 0 < n) {V : Set (Fin n → ℝ)}
    (hconv : Convex ℝ V)
    (hcone : ∀ v ∈ V, ∀ (c : ℝ), c > 0 → (fun i => c * v i) ∈ V)
    (v : Fin n → (Fin n → ℝ)) (hv : ∀ j, v j ∈ V) (x : Fin n → ℝ) (w : Fin n → ℂ)
    (hw : ∀ j, 0 < (w j).im) :
    cAffine (Matrix.of fun i j => v j i) x w ∈ TubeDomain V := by
  change (fun i => (cAffine (Matrix.of fun i j => v j i) x w i).im) ∈ V
  rw [cAffine_im]
  have h : Matrix.mulVec (Matrix.of fun i j => v j i) (fun j => (w j).im) =
      ∑ j, (w j).im • v j := by
    ext i
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  rw [h]
  exact sum_pos_smul_mem_of_convex_cone hn hconv hcone v hv _ hw

lemma cAffine_mem_tube_minus {n : ℕ} (hn : 0 < n) {V : Set (Fin n → ℝ)}
    (hconv : Convex ℝ V)
    (hcone : ∀ v ∈ V, ∀ (c : ℝ), c > 0 → (fun i => c * v i) ∈ V)
    (v : Fin n → (Fin n → ℝ)) (hv : ∀ j, v j ∈ V) (x : Fin n → ℝ) (w : Fin n → ℂ)
    (hw : ∀ j, (w j).im < 0) :
    cAffine (Matrix.of fun i j => v j i) x w ∈
      TubeDomain ((fun u : Fin n → ℝ => -u) '' V) := by
  change (fun i => (cAffine (Matrix.of fun i j => v j i) x w i).im) ∈
    ((fun u : Fin n → ℝ => -u) '' V)
  rw [cAffine_im]
  have h : Matrix.mulVec (Matrix.of fun i j => v j i) (fun j => (w j).im) =
      -∑ j, (-(w j).im) • v j := by
    ext i
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm, Finset.sum_neg_distrib]
  rw [h]
  exact ⟨_, sum_pos_smul_mem_of_convex_cone hn hconv hcone v hv _ (fun j => neg_pos.mpr (hw j)),
    rfl⟩

def PosOrthant (n : ℕ) : Set (Fin n → ℝ) := {y | ∀ j, 0 < y j}

def NegOrthant (n : ℕ) : Set (Fin n → ℝ) := {y | ∀ j, y j < 0}

lemma isOpen_PosOrthant (n : ℕ) : IsOpen (PosOrthant n) := by
  have : PosOrthant n = ⋂ j, (fun y : Fin n → ℝ => y j) ⁻¹' Set.Ioi (0 : ℝ) := by
    ext y; simp [PosOrthant]
  rw [this]
  exact isOpen_iInter_of_finite (fun j => isOpen_Ioi.preimage (continuous_apply j))

lemma isOpen_NegOrthant (n : ℕ) : IsOpen (NegOrthant n) := by
  have : NegOrthant n = ⋂ j, (fun y : Fin n → ℝ => y j) ⁻¹' Set.Iio (0 : ℝ) := by
    ext y; simp [NegOrthant]
  rw [this]
  exact isOpen_iInter_of_finite (fun j => isOpen_Iio.preimage (continuous_apply j))

def OrthantEOWCore (n : ℕ) (g : (Fin n → ℂ) → ℂ) : Prop :=
  ∃ ρ : ℝ, 0 < ρ ∧ ∃ G : (Fin n → ℂ) → ℂ,
    AnalyticOnNhd ℂ G (Metric.ball 0 ρ) ∧
    (∃ W : Set (Fin n → ℂ), IsOpen W ∧ W.Nonempty ∧
      W ⊆ Metric.ball 0 ρ ∩ TubeDomain (PosOrthant n) ∧ EqOn G g W) ∧
    (∃ W : Set (Fin n → ℂ), IsOpen W ∧ W.Nonempty ∧
      W ⊆ Metric.ball 0 ρ ∩ TubeDomain (NegOrthant n) ∧ EqOn G g W)

lemma convex_PosOrthant (n : ℕ) : Convex ℝ (PosOrthant n) := by
  intro x hx y hy a b ha hb _hab j
  dsimp [PosOrthant] at hx hy ⊢
  change 0 < a * x j + b * y j
  rcases ha.eq_or_lt with rfl | ha_pos
  · have hb1 : b = 1 := by linarith
    subst hb1
    nlinarith [hy j]
  · have : 0 ≤ b * y j := mul_nonneg hb (hy j).le
    have : 0 < a * x j := mul_pos ha_pos (hx j)
    linarith

lemma convex_NegOrthant (n : ℕ) : Convex ℝ (NegOrthant n) := by
  intro x hx y hy a b ha hb _hab j
  dsimp [NegOrthant] at hx hy ⊢
  change a * x j + b * y j < 0
  rcases ha.eq_or_lt with rfl | ha_pos
  · have hb1 : b = 1 := by linarith
    subst hb1
    nlinarith [hy j]
  · have : b * y j ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hb (hy j).le
    have : a * x j < 0 := mul_neg_of_pos_of_neg ha_pos (hx j)
    linarith

lemma orthantEOWCore_eqOn_plus {n : ℕ} (g : (Fin n → ℂ) → ℂ)
    (hg_diff : DifferentiableOn ℂ g (TubeDomain (PosOrthant n)))
    {ρ : ℝ} (_hρ : 0 < ρ) {G : (Fin n → ℂ) → ℂ}
    (hG_an : AnalyticOnNhd ℂ G (Metric.ball 0 ρ))
    {W : Set (Fin n → ℂ)} (hW_open : IsOpen W) (hW_ne : W.Nonempty)
    (hW_sub : W ⊆ Metric.ball 0 ρ ∩ TubeDomain (PosOrthant n))
    (hW_eq : EqOn G g W) :
    EqOn G g (Metric.ball 0 ρ ∩ TubeDomain (PosOrthant n)) := by
  have hS_open : IsOpen (Metric.ball 0 ρ ∩ TubeDomain (PosOrthant n)) :=
    Metric.isOpen_ball.inter (isOpen_TubeDomain (isOpen_PosOrthant n))
  have hS_conv : Convex ℝ (Metric.ball 0 ρ ∩ TubeDomain (PosOrthant n)) :=
    (convex_ball 0 ρ).inter (convex_TubeDomain (convex_PosOrthant n))
  have hd : DifferentiableOn ℂ (G - g) (Metric.ball 0 ρ ∩ TubeDomain (PosOrthant n)) :=
    (hG_an.differentiableOn.mono Set.inter_subset_left).sub
      (hg_diff.mono Set.inter_subset_right)
  have h0 := eqOn_zero_of_convex_differentiableOn hS_open hS_conv hd hW_open hW_sub hW_ne
    (fun z hz => by simp [hW_eq hz])
  intro z hz
  simpa [sub_eq_zero] using h0 hz

lemma orthantEOWCore_eqOn_minus {n : ℕ} (g : (Fin n → ℂ) → ℂ)
    (hg_diff : DifferentiableOn ℂ g (TubeDomain (NegOrthant n)))
    {ρ : ℝ} (_hρ : 0 < ρ) {G : (Fin n → ℂ) → ℂ}
    (hG_an : AnalyticOnNhd ℂ G (Metric.ball 0 ρ))
    {W : Set (Fin n → ℂ)} (hW_open : IsOpen W) (hW_ne : W.Nonempty)
    (hW_sub : W ⊆ Metric.ball 0 ρ ∩ TubeDomain (NegOrthant n))
    (hW_eq : EqOn G g W) :
    EqOn G g (Metric.ball 0 ρ ∩ TubeDomain (NegOrthant n)) := by
  have hS_open : IsOpen (Metric.ball 0 ρ ∩ TubeDomain (NegOrthant n)) :=
    Metric.isOpen_ball.inter (isOpen_TubeDomain (isOpen_NegOrthant n))
  have hS_conv : Convex ℝ (Metric.ball 0 ρ ∩ TubeDomain (NegOrthant n)) :=
    (convex_ball 0 ρ).inter (convex_TubeDomain (convex_NegOrthant n))
  have hd : DifferentiableOn ℂ (G - g) (Metric.ball 0 ρ ∩ TubeDomain (NegOrthant n)) :=
    (hG_an.differentiableOn.mono Set.inter_subset_left).sub
      (hg_diff.mono Set.inter_subset_right)
  have h0 := eqOn_zero_of_convex_differentiableOn hS_open hS_conv hd hW_open hW_sub hW_ne
    (fun z hz => by simp [hW_eq hz])
  intro z hz
  simpa [sub_eq_zero] using h0 hz

lemma eow_local_core_of_orthant {n : ℕ} (hn : 0 < n) (V_plus : Set (Fin n → ℝ))
    (_hV_plus_open : IsOpen V_plus)
    (hV_plus_convex : Convex ℝ V_plus)
    (hV_plus_cone : ∀ v ∈ V_plus, ∀ (c : ℝ), c > 0 → (fun i => c * v i) ∈ V_plus)
    (f : (Fin n → ℂ) → ℂ)
    (h_holo_plus : DifferentiableOn ℂ f (TubeDomain V_plus))
    (h_holo_minus : DifferentiableOn ℂ f (TubeDomain ((fun v : Fin n → ℝ => -v) '' V_plus)))
    (x : Fin n → ℝ)
    (v : Fin n → (Fin n → ℝ)) (hli : LinearIndependent ℝ v) (hv : ∀ j, v j ∈ V_plus)
    (h_core : OrthantEOWCore n (f ∘ cAffine (Matrix.of fun i j => v j i) x)) :
    LocalEOWCore V_plus f x := by
  let M : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => v j i
  have hM_unit : IsUnit M := isUnit_of_linearIndependent_cols v hli
  obtain ⟨Ψ, hΨ_diff, hΨ_an, hcAffine_inv, hΨ_inv⟩ := exists_inverse_cAffine M hM_unit x
  rcases h_core with ⟨ρ, hρ_pos, G, hG_an,
    ⟨W₁, hW₁o, hW₁n, hW₁s, hW₁e⟩, ⟨W₂, hW₂o, hW₂n, hW₂s, hW₂e⟩⟩
  have hΨ_cont : Continuous Ψ := hΨ_diff.continuous
  have hcAffine_0 : cAffine M x 0 = fun i => (x i : ℂ) := by
    ext i; simp [cAffine]
  have hΨ_xc : Ψ (fun i => (x i : ℂ)) = 0 := by
    rw [← hcAffine_0, hΨ_inv 0]
  have h_open_pre : IsOpen (Ψ ⁻¹' (Metric.ball 0 ρ)) := Metric.isOpen_ball.preimage hΨ_cont
  have h_xc_in : (fun i => (x i : ℂ)) ∈ Ψ ⁻¹' (Metric.ball 0 ρ) := by
    simp [hΨ_xc, Metric.mem_ball_self hρ_pos]
  rcases Metric.isOpen_iff.mp h_open_pre _ h_xc_in with ⟨r, hr_pos, hr_sub⟩
  let F : (Fin n → ℂ) → ℂ := G ∘ Ψ
  have hF_an : AnalyticOnNhd ℂ F (Metric.ball (fun i => (x i : ℂ)) r) := by
    intro z hz
    have hz_in : Ψ z ∈ Metric.ball 0 ρ := hr_sub hz
    exact (hG_an (Ψ z) hz_in).comp (hΨ_an z)
  have hg_diff_plus : DifferentiableOn ℂ (f ∘ cAffine M x) (TubeDomain (PosOrthant n)) :=
    h_holo_plus.comp (differentiable_cAffine M x).differentiableOn
      (fun w hw => cAffine_mem_tube_plus hn hV_plus_convex hV_plus_cone v hv x w hw)
  have h_eq₁ := orthantEOWCore_eqOn_plus (f ∘ cAffine M x)
    hg_diff_plus hρ_pos hG_an hW₁o hW₁n hW₁s hW₁e
  have hg_diff_minus : DifferentiableOn ℂ (f ∘ cAffine M x) (TubeDomain (NegOrthant n)) :=
    h_holo_minus.comp (differentiable_cAffine M x).differentiableOn
      (fun w hw => cAffine_mem_tube_minus hn hV_plus_convex hV_plus_cone v hv x w hw)
  have h_eq₂ := orthantEOWCore_eqOn_minus (f ∘ cAffine M x)
    hg_diff_minus hρ_pos hG_an hW₂o hW₂n hW₂s hW₂e
  refine ⟨r, hr_pos, F, hF_an, ?_, ?_⟩
  · let W₁' : Set (Fin n → ℂ) :=
      Ψ ⁻¹' (Metric.ball 0 ρ ∩ TubeDomain (PosOrthant n)) ∩ Metric.ball (fun i => (x i : ℂ)) r
    have hW₁'_open : IsOpen W₁' :=
      (Metric.isOpen_ball.inter (isOpen_TubeDomain (isOpen_PosOrthant n))).preimage
        hΨ_cont |>.inter Metric.isOpen_ball
    have hW₁'_sub : W₁' ⊆ Metric.ball (fun i => (x i : ℂ)) r ∩ TubeDomain V_plus := by
      rintro z ⟨⟨_hz_ball_ρ, hz_tube_orth⟩, hz_ball_r⟩
      refine ⟨hz_ball_r, ?_⟩
      have h := cAffine_mem_tube_plus hn hV_plus_convex hV_plus_cone v hv x (Ψ z) hz_tube_orth
      rwa [hcAffine_inv z] at h
    have hW₁'_eq : EqOn F f W₁' := by
      rintro z ⟨hz_orth, _⟩
      dsimp [F]
      have h1 := h_eq₁ hz_orth
      dsimp [Function.comp] at h1
      rw [h1, hcAffine_inv z]
    have h_cAff_cont : Continuous (cAffine M x) := (differentiable_cAffine M x).continuous
    have h_tend : Filter.Tendsto (cAffine M x) (nhds 0) (nhds (fun i => (x i : ℂ))) := by
      rw [← hcAffine_0]
      exact h_cAff_cont.continuousAt
    have h_ball_nhd : Metric.ball (fun i => (x i : ℂ)) r ∈ nhds (fun i => (x i : ℂ)) :=
      Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr_pos)
    have h_pre_nhd : Metric.ball 0 ρ ∈ nhds (0 : Fin n → ℂ) :=
      Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hρ_pos)
    let curve : ℝ → (Fin n → ℂ) := fun t => fun _ => (t : ℂ) * Complex.I
    have hcurve_cont : Continuous curve := by
      unfold curve; fun_prop
    have hcurve_0 : curve 0 = 0 := by ext i; simp [curve]
    have h_ev_ball_ρ : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0), curve t ∈ Metric.ball 0 ρ := by
      have htend : Filter.Tendsto curve (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
        rw [← hcurve_0]
        exact hcurve_cont.continuousAt.mono_left nhdsWithin_le_nhds
      exact htend h_pre_nhd
    have h_ev_ball_r : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0),
        cAffine M x (curve t) ∈ Metric.ball (fun i => (x i : ℂ)) r := by
      have htend : Filter.Tendsto (cAffine M x ∘ curve) (nhdsWithin 0 (Set.Ioi 0))
          (nhds (fun i => (x i : ℂ))) := by
        refine h_tend.comp ?_
        rw [← hcurve_0]
        exact hcurve_cont.continuousAt.mono_left nhdsWithin_le_nhds
      exact htend h_ball_nhd
    have h_ev_pos : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < t := self_mem_nhdsWithin
    obtain ⟨t, ⟨ht_bρ, ht_br⟩, ht_pos⟩ := (h_ev_ball_ρ.and h_ev_ball_r).and h_ev_pos |>.exists
    have hw₀_pos : ∀ j, 0 < (curve t j).im := by
      intro j
      dsimp [curve]
      simp [Complex.mul_im, ht_pos]
    have hz₀_in : cAffine M x (curve t) ∈ W₁' := by
      refine ⟨?_, ht_br⟩
      rw [Set.mem_preimage, hΨ_inv (curve t)]
      exact ⟨ht_bρ, hw₀_pos⟩
    exact ⟨W₁', hW₁'_open, ⟨cAffine M x (curve t), hz₀_in⟩, hW₁'_sub, hW₁'_eq⟩
  · let W₂' : Set (Fin n → ℂ) :=
      Ψ ⁻¹' (Metric.ball 0 ρ ∩ TubeDomain (NegOrthant n)) ∩ Metric.ball (fun i => (x i : ℂ)) r
    have hW₂'_open : IsOpen W₂' :=
      (Metric.isOpen_ball.inter (isOpen_TubeDomain (isOpen_NegOrthant n))).preimage
        hΨ_cont |>.inter Metric.isOpen_ball
    have hW₂'_sub : W₂' ⊆
        Metric.ball (fun i => (x i : ℂ)) r ∩ TubeDomain ((fun v => -v) '' V_plus) := by
      rintro z ⟨⟨_hz_ball_ρ, hz_tube_orth⟩, hz_ball_r⟩
      refine ⟨hz_ball_r, ?_⟩
      have h := cAffine_mem_tube_minus hn hV_plus_convex hV_plus_cone v hv x (Ψ z) hz_tube_orth
      rwa [hcAffine_inv z] at h
    have hW₂'_eq : EqOn F f W₂' := by
      rintro z ⟨hz_orth, _⟩
      dsimp [F]
      have h1 := h_eq₂ hz_orth
      dsimp [Function.comp] at h1
      rw [h1, hcAffine_inv z]
    have h_cAff_cont : Continuous (cAffine M x) := (differentiable_cAffine M x).continuous
    have h_tend : Filter.Tendsto (cAffine M x) (nhds 0) (nhds (fun i => (x i : ℂ))) := by
      rw [← hcAffine_0]
      exact h_cAff_cont.continuousAt
    have h_ball_nhd : Metric.ball (fun i => (x i : ℂ)) r ∈ nhds (fun i => (x i : ℂ)) :=
      Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr_pos)
    have h_pre_nhd : Metric.ball 0 ρ ∈ nhds (0 : Fin n → ℂ) :=
      Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hρ_pos)
    let curve : ℝ → (Fin n → ℂ) := fun t => fun _ => - ((t : ℂ) * Complex.I)
    have hcurve_cont : Continuous curve := by
      unfold curve; fun_prop
    have hcurve_0 : curve 0 = 0 := by ext i; simp [curve]
    have h_ev_ball_ρ : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0), curve t ∈ Metric.ball 0 ρ := by
      have htend : Filter.Tendsto curve (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
        rw [← hcurve_0]
        exact hcurve_cont.continuousAt.mono_left nhdsWithin_le_nhds
      exact htend h_pre_nhd
    have h_ev_ball_r : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0),
        cAffine M x (curve t) ∈ Metric.ball (fun i => (x i : ℂ)) r := by
      have htend : Filter.Tendsto (cAffine M x ∘ curve) (nhdsWithin 0 (Set.Ioi 0))
          (nhds (fun i => (x i : ℂ))) := by
        refine h_tend.comp ?_
        rw [← hcurve_0]
        exact hcurve_cont.continuousAt.mono_left nhdsWithin_le_nhds
      exact htend h_ball_nhd
    have h_ev_pos : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < t := self_mem_nhdsWithin
    obtain ⟨t, ⟨ht_bρ, ht_br⟩, ht_pos⟩ := (h_ev_ball_ρ.and h_ev_ball_r).and h_ev_pos |>.exists
    have hw₀_neg : ∀ j, (curve t j).im < 0 := by
      intro j
      dsimp [curve]
      simp [Complex.mul_im, ht_pos]
    have hz₀_in : cAffine M x (curve t) ∈ W₂' := by
      refine ⟨?_, ht_br⟩
      rw [Set.mem_preimage, hΨ_inv (curve t)]
      exact ⟨ht_bρ, hw₀_neg⟩
    exact ⟨W₂', hW₂'_open, ⟨cAffine M x (curve t), hz₀_in⟩, hW₂'_sub, hW₂'_eq⟩

lemma div_add_one_mul_lt {r v : ℝ} (hr : 0 < r) (hv : 0 ≤ v) :
    ((r / 2) / (v + 1)) * v < r := by
  have hv1 : 0 < v + 1 := by linarith
  have h1 : v / (v + 1) < 1 := (div_lt_one hv1).mpr (lt_add_one v)
  have h2 : ((r / 2) / (v + 1)) * v = (r / 2) * (v / (v + 1)) := by ring
  rw [h2]
  calc (r / 2) * (v / (v + 1))
    _ < (r / 2) * 1 := mul_lt_mul_of_pos_left h1 (half_pos hr)
    _ = r / 2 := mul_one _
    _ < r := half_lt_self hr

lemma eow_local_core_0d (V_plus _U : Set (Fin 0 → ℝ))
    (hV_plus_ne : V_plus.Nonempty)
    (f : (Fin 0 → ℂ) → ℂ)
    (x : Fin 0 → ℝ) :
    LocalEOWCore V_plus f x := by
  refine ⟨1, by positivity, f, ?_, ?_, ?_⟩
  · have heq : f = fun _ => f (fun _ => 0) := by
      ext y; congr; ext i; exact Fin.elim0 i
    rw [heq]
    intro z _hz
    exact analyticAt_const
  · refine ⟨Metric.ball (fun i => (x i : ℂ)) 1, Metric.isOpen_ball,
      Metric.nonempty_ball.mpr (by positivity), ?_, fun z _ => rfl⟩
    intro z hz
    refine ⟨hz, ?_⟩
    change (fun i => (z i).im) ∈ V_plus
    obtain ⟨v0, hv0⟩ := hV_plus_ne
    have hv0_eq : v0 = (fun i => (z i).im) := by ext i; exact Fin.elim0 i
    rw [← hv0_eq]
    exact hv0
  · refine ⟨Metric.ball (fun i => (x i : ℂ)) 1, Metric.isOpen_ball,
      Metric.nonempty_ball.mpr (by positivity), ?_, fun z _ => rfl⟩
    intro z hz
    refine ⟨hz, ?_⟩
    obtain ⟨v0, hv0⟩ := hV_plus_ne
    refine ⟨v0, hv0, ?_⟩
    ext i
    exact Fin.elim0 i

lemma eow_local_core_1d (V_plus U : Set (Fin 1 → ℝ))
    (hV_plus_open : IsOpen V_plus)
    (hV_plus_cone : ∀ v ∈ V_plus, ∀ (c : ℝ), c > 0 → (fun i => c * v i) ∈ V_plus)
    (hV_plus_ne : V_plus.Nonempty)
    (hU_open : IsOpen U)
    (f : (Fin 1 → ℂ) → ℂ)
    (h_cont : ContinuousOn f (WedgeDomain V_plus ((fun v : Fin 1 → ℝ => -v) '' V_plus) U))
    (h_holo_plus : DifferentiableOn ℂ f (TubeDomain V_plus))
    (h_holo_minus : DifferentiableOn ℂ f (TubeDomain ((fun v : Fin 1 → ℝ => -v) '' V_plus)))
    (x : Fin 1 → ℝ) (hx_U : x ∈ U) :
    LocalEOWCore V_plus f x := by
  rcases Metric.isOpen_iff.mp hU_open x hx_U with ⟨r_U, hr_U_pos, hr_U_sub⟩
  rcases exists_local_analytic_extension_cauchy_1d V_plus U hV_plus_open hV_plus_cone
    hV_plus_ne hU_open f h_cont h_holo_plus h_holo_minus x hx_U r_U hr_U_pos hr_U_sub with
    ⟨F_1, hF_ana, hF_eq⟩
  rcases analyticOnNhd_ball_of_analyticAt hF_ana with ⟨ρ, hρ_pos, hF_nhd⟩
  let r := min ρ r_U
  have hr_pos : 0 < r := lt_min hρ_pos hr_U_pos
  refine ⟨r, hr_pos, F_1, hF_nhd.mono (Metric.ball_subset_ball (min_le_left _ _)), ?_, ?_⟩
  · let W₁ := Metric.ball (fun i => (x i : ℂ)) r ∩ TubeDomain V_plus
    have hW₁_open : IsOpen W₁ := Metric.isOpen_ball.inter (isOpen_TubeDomain hV_plus_open)
    obtain ⟨v, hv, _⟩ := exists_ne_zero_of_open_cone_1d V_plus hV_plus_open hV_plus_cone hV_plus_ne
    have h_norm_v : 0 < ‖v 0‖ + 1 := by positivity
    let t := (r / 2) / (‖v 0‖ + 1)
    have ht_pos : 0 < t := div_pos (half_pos hr_pos) h_norm_v
    let z : Fin 1 → ℂ := fun i => (x i : ℂ) + (t : ℂ) * Complex.I * (v i : ℂ)
    have hz_im : (fun i => (z i).im) = fun i => t * v i := by
      ext i; simp [z, Complex.mul_im]
    have hz_tube : z ∈ TubeDomain V_plus := by
      change (fun i => (z i).im) ∈ V_plus
      rw [hz_im]
      exact hV_plus_cone v hv t ht_pos
    have hz_ball : z ∈ Metric.ball (fun i => (x i : ℂ)) r := by
      rw [Metric.mem_ball]
      apply (dist_pi_lt_iff hr_pos).mpr
      intro i
      fin_cases i
      dsimp [z]
      rw [dist_eq_norm]
      have heq : (x 0 : ℂ) + (t : ℂ) * Complex.I * (v 0 : ℂ) - (x 0 : ℂ) =
          (t : ℂ) * Complex.I * (v 0 : ℂ) := by ring
      rw [heq, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_of_nonneg ht_pos.le, Complex.norm_real]
      exact div_add_one_mul_lt hr_pos (norm_nonneg _)
    have hW₁_ne : W₁.Nonempty := ⟨z, hz_ball, hz_tube⟩
    refine ⟨W₁, hW₁_open, hW₁_ne, subset_rfl, ?_⟩
    intro w hw
    have hw_ball_rU : w ∈ Metric.ball (fun i => (x i : ℂ)) r_U :=
      (Metric.ball_subset_ball (min_le_right ρ r_U)) hw.1
    have hw_wedge : w ∈ WedgeDomain V_plus ((fun v => -v) '' V_plus) U :=
      Or.inl (Or.inl hw.2)
    exact hF_eq ⟨hw_ball_rU, hw_wedge⟩
  · let W₂ := Metric.ball (fun i => (x i : ℂ)) r ∩ TubeDomain ((fun v => -v) '' V_plus)
    have hW₂_open : IsOpen W₂ :=
      Metric.isOpen_ball.inter (isOpen_TubeDomain_minus V_plus hV_plus_open)
    obtain ⟨v, hv, _⟩ := exists_ne_zero_of_open_cone_1d V_plus hV_plus_open hV_plus_cone hV_plus_ne
    have h_norm_v : 0 < ‖v 0‖ + 1 := by positivity
    let t := (r / 2) / (‖v 0‖ + 1)
    have ht_pos : 0 < t := div_pos (half_pos hr_pos) h_norm_v
    let z : Fin 1 → ℂ := fun i => (x i : ℂ) - (t : ℂ) * Complex.I * (v i : ℂ)
    have hz_im : (fun i => (z i).im) = fun i => - (t * v i) := by
      ext i; simp [z, Complex.sub_im, Complex.mul_im]
    have hz_tube : z ∈ TubeDomain ((fun v => -v) '' V_plus) := by
      change (fun i => (z i).im) ∈ ((fun v => -v) '' V_plus)
      rw [hz_im]
      refine ⟨fun i => t * v i, hV_plus_cone v hv t ht_pos, ?_⟩
      ext i; simp
    have hz_ball : z ∈ Metric.ball (fun i => (x i : ℂ)) r := by
      rw [Metric.mem_ball]
      apply (dist_pi_lt_iff hr_pos).mpr
      intro i
      fin_cases i
      dsimp [z]
      rw [dist_eq_norm]
      have heq : (x 0 : ℂ) - (t : ℂ) * Complex.I * (v 0 : ℂ) - (x 0 : ℂ) =
          - ((t : ℂ) * Complex.I * (v 0 : ℂ)) := by ring
      rw [heq, norm_neg, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
        Real.norm_of_nonneg ht_pos.le, Complex.norm_real]
      exact div_add_one_mul_lt hr_pos (norm_nonneg _)
    have hW₂_ne : W₂.Nonempty := ⟨z, hz_ball, hz_tube⟩
    refine ⟨W₂, hW₂_open, hW₂_ne, subset_rfl, ?_⟩
    intro w hw
    have hw_ball_rU : w ∈ Metric.ball (fun i => (x i : ℂ)) r_U :=
      (Metric.ball_subset_ball (min_le_right ρ r_U)) hw.1
    have hw_wedge : w ∈ WedgeDomain V_plus ((fun v => -v) '' V_plus) U :=
      Or.inl (Or.inr hw.2)
    exact hF_eq ⟨hw_ball_rU, hw_wedge⟩

lemma orthant_eow_core_1d
    (V_plus U : Set (Fin 1 → ℝ))
    (hV_plus_open : IsOpen V_plus)
    (hV_plus_cone : ∀ v ∈ V_plus, ∀ (c : ℝ), c > 0 → (fun i => c * v i) ∈ V_plus)
    (hU_open : IsOpen U)
    (f : (Fin 1 → ℂ) → ℂ)
    (h_cont : ContinuousOn f (WedgeDomain V_plus ((fun v : Fin 1 → ℝ => -v) '' V_plus) U))
    (h_holo_plus : DifferentiableOn ℂ f (TubeDomain V_plus))
    (h_holo_minus : DifferentiableOn ℂ f (TubeDomain ((fun v : Fin 1 → ℝ => -v) '' V_plus)))
    (x : Fin 1 → ℝ) (hx_U : x ∈ U)
    (v : Fin 1 → (Fin 1 → ℝ)) (_hli : LinearIndependent ℝ v) (hv : ∀ j, v j ∈ V_plus) :
    OrthantEOWCore 1 (f ∘ cAffine (Matrix.of fun i j => v j i) x) := by
  let M : Matrix (Fin 1) (Fin 1) ℝ := Matrix.of fun i j => v j i
  have h_slice := slice_analytic_at_zero V_plus U hV_plus_open hV_plus_cone hU_open f h_cont
    h_holo_plus h_holo_minus x hx_U (v 0) (hv 0)
  rcases Metric.mem_nhds_iff.mp h_slice.eventually_analyticAt with ⟨ρ, hρ_pos, hg_an⟩
  let G : (Fin 1 → ℂ) → ℂ := fun w => slice_fun f (fun i => (x i : ℂ)) (v 0) (w 0)
  have hG_an : AnalyticOnNhd ℂ G (Metric.ball 0 ρ) := by
    intro w hw
    have hw0 : w 0 ∈ Metric.ball 0 ρ := by
      rw [Metric.mem_ball] at hw ⊢
      have hle := dist_le_pi_dist w 0 0
      exact lt_of_le_of_lt hle hw
    let P : (Fin 1 → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj (0 : Fin 1)
    have hP : AnalyticAt ℂ P w := P.analyticAt w
    exact AnalyticAt.comp (f := P) (hg_an hw0) hP
  refine ⟨ρ, hρ_pos, G, hG_an, ?_, ?_⟩
  · let W₁ := Metric.ball (0 : Fin 1 → ℂ) ρ ∩ TubeDomain (PosOrthant 1)
    have hW₁_open : IsOpen W₁ := Metric.isOpen_ball.inter (isOpen_TubeDomain (isOpen_PosOrthant 1))
    have hW₁_ne : W₁.Nonempty := by
      let z : Fin 1 → ℂ := fun _ => ((ρ / 2 : ℝ) : ℂ) * Complex.I
      refine ⟨z, ?_⟩
      refine ⟨?_, ?_⟩
      · rw [Metric.mem_ball]
        apply (dist_pi_lt_iff hρ_pos).mpr
        intro i; fin_cases i
        dsimp [z]
        rw [dist_zero_right, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
          Real.norm_of_nonneg (half_pos hρ_pos).le]
        exact half_lt_self hρ_pos
      · intro i; fin_cases i
        dsimp [z]
        simp [Complex.mul_im, half_pos hρ_pos]
    refine ⟨W₁, hW₁_open, hW₁_ne, subset_rfl, ?_⟩
    intro w _hw
    dsimp [G, Function.comp, slice_fun]
    congr 1
    ext i; fin_cases i
    simp [cAffine, Matrix.mulVec, dotProduct]
    ring
  · let W₂ := Metric.ball (0 : Fin 1 → ℂ) ρ ∩ TubeDomain (NegOrthant 1)
    have hW₂_open : IsOpen W₂ := Metric.isOpen_ball.inter (isOpen_TubeDomain (isOpen_NegOrthant 1))
    have hW₂_ne : W₂.Nonempty := by
      let z : Fin 1 → ℂ := fun _ => - (((ρ / 2 : ℝ) : ℂ) * Complex.I)
      refine ⟨z, ?_⟩
      refine ⟨?_, ?_⟩
      · rw [Metric.mem_ball]
        apply (dist_pi_lt_iff hρ_pos).mpr
        intro i; fin_cases i
        dsimp [z]
        rw [dist_zero_right, norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
          Real.norm_of_nonneg (half_pos hρ_pos).le]
        exact half_lt_self hρ_pos
      · intro i; fin_cases i
        dsimp [z]
        simp [Complex.mul_im, half_pos hρ_pos]
    refine ⟨W₂, hW₂_open, hW₂_ne, subset_rfl, ?_⟩
    intro w _hw
    dsimp [G, Function.comp, slice_fun]
    congr 1
    ext i; fin_cases i
    simp [cAffine, Matrix.mulVec, dotProduct]
    ring

lemma eow_orthant_core {n : ℕ} (hn : n = 1)
    (V_plus U : Set (Fin n → ℝ))
    (hV_plus_open : IsOpen V_plus)
    (hV_plus_convex : Convex ℝ V_plus)
    (hV_plus_cone : ∀ v ∈ V_plus, ∀ (c : ℝ), c > 0 → (fun i => c * v i) ∈ V_plus)
    (hU_open : IsOpen U)
    (f : (Fin n → ℂ) → ℂ)
    (h_cont : ContinuousOn f (WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U))
    (h_holo_plus : DifferentiableOn ℂ f (TubeDomain V_plus))
    (h_holo_minus : DifferentiableOn ℂ f (TubeDomain ((fun v : Fin n → ℝ => -v) '' V_plus)))
    (x : Fin n → ℝ) (hx_U : x ∈ U)
    (v : Fin n → (Fin n → ℝ)) (hli : LinearIndependent ℝ v) (hv : ∀ j, v j ∈ V_plus) :
    OrthantEOWCore n (f ∘ cAffine (Matrix.of fun i j => v j i) x) := by
  subst hn
  exact orthant_eow_core_1d V_plus U hV_plus_open hV_plus_cone hU_open f h_cont
    h_holo_plus h_holo_minus x hx_U v hli hv

lemma eow_local_core {n : ℕ} (hn_le : n ≤ 1) (V_plus U : Set (Fin n → ℝ))
    (hV_plus_open : IsOpen V_plus)
    (_hV_plus_convex : Convex ℝ V_plus)
    (hV_plus_cone : ∀ v ∈ V_plus, ∀ (c : ℝ), c > 0 → (fun i => c * v i) ∈ V_plus)
    (hV_plus_ne : V_plus.Nonempty)
    (hU_open : IsOpen U)
    (f : (Fin n → ℂ) → ℂ)
    (h_cont : ContinuousOn f (WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U))
    (h_holo_plus : DifferentiableOn ℂ f (TubeDomain V_plus))
    (h_holo_minus : DifferentiableOn ℂ f (TubeDomain ((fun v : Fin n → ℝ => -v) '' V_plus)))
    (x : Fin n → ℝ) (hx_U : x ∈ U) :
    LocalEOWCore V_plus f x := by
  by_cases h0 : n = 0
  · subst h0
    exact eow_local_core_0d V_plus U hV_plus_ne f x
  · have h1 : n = 1 := by omega
    subst h1
    exact eow_local_core_1d V_plus U hV_plus_open hV_plus_cone hV_plus_ne hU_open f
      h_cont h_holo_plus h_holo_minus x hx_U

lemma exists_local_analytic_extension_cauchy {n : ℕ} (hn_le : n ≤ 1) (V_plus U : Set (Fin n → ℝ))
    (hV_plus_open : IsOpen V_plus)
    (_hV_plus_convex : Convex ℝ V_plus)
    (hV_plus_cone : ∀ v ∈ V_plus, ∀ (c : ℝ), c > 0 → (fun i => c * v i) ∈ V_plus)
    (hV_plus_ne : V_plus.Nonempty)
    (hU_open : IsOpen U)
    (f : (Fin n → ℂ) → ℂ)
    (h_cont : ContinuousOn f (WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U))
    (h_holo_plus : DifferentiableOn ℂ f (TubeDomain V_plus))
    (h_holo_minus : DifferentiableOn ℂ f (TubeDomain ((fun v : Fin n → ℝ => -v) '' V_plus)))
    (x : Fin n → ℝ) (hx_U : x ∈ U) (r : ℝ) (hr : 0 < r)
    (h_ball_U : Metric.ball x r ⊆ U) :
    ∃ F_x : (Fin n → ℂ) → ℂ,
      AnalyticAt ℂ F_x (fun i => (x i : ℂ)) ∧
      EqOn F_x f (Metric.ball (fun i => (x i : ℂ)) r ∩
        WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U) := by
  by_cases h_dim0 : n = 0
  · subst h_dim0
    use f
    refine ⟨?_, fun z _ => rfl⟩
    have heq : f = fun _ => f (fun _ => 0) := by
      ext y; congr; ext i; exact Fin.elim0 i
    rw [heq]
    exact analyticAt_const
  · have h_dim1 : n = 1 := by omega
    subst h_dim1
    exact exists_local_analytic_extension_cauchy_1d V_plus U hV_plus_open hV_plus_cone
      hV_plus_ne hU_open f h_cont h_holo_plus h_holo_minus x hx_U r hr h_ball_U

lemma eow_local_analytic_at {n : ℕ} (hn_le : n ≤ 1) (V_plus U : Set (Fin n → ℝ))
    (hV_plus_open : IsOpen V_plus)
    (hV_plus_convex : Convex ℝ V_plus)
    (hV_plus_cone : ∀ v ∈ V_plus, ∀ (c : ℝ), c > 0 → (fun i => c * v i) ∈ V_plus)
    (hV_plus_ne : V_plus.Nonempty)
    (hU_open : IsOpen U)
    (f : (Fin n → ℂ) → ℂ)
    (h_cont : ContinuousOn f (WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U))
    (h_holo_plus : DifferentiableOn ℂ f (TubeDomain V_plus))
    (h_holo_minus : DifferentiableOn ℂ f (TubeDomain ((fun v : Fin n → ℝ => -v) '' V_plus)))
    (x : Fin n → ℝ) (hx_U : x ∈ U) :
    ∃ (F_x : (Fin n → ℂ) → ℂ) (r : ℝ), 0 < r ∧
      AnalyticAt ℂ F_x (fun i => (x i : ℂ)) ∧
      EqOn F_x f (Metric.ball (fun i => (x i : ℂ)) r ∩
        WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U) := by
  rcases Metric.isOpen_iff.mp hU_open x hx_U with ⟨r_U, hr_U_pos, hr_U_sub⟩
  have ⟨v, hv⟩ := hV_plus_ne
  by_cases h_dim : n = 0
  · subst h_dim
    use f, 1
    refine ⟨by positivity, ?_, ?_⟩
    · have heq : f = fun _ => f (fun _ => 0) := by
        ext y
        congr
        ext i
        exact Fin.elim0 i
      rw [heq]
      exact analyticAt_const
    · intro z _
      rfl
  · have h_slice := slice_analytic_at_zero V_plus U hV_plus_open hV_plus_cone hU_open f h_cont
      h_holo_plus h_holo_minus x hx_U v hv
    have h_open : IsOpen {w | AnalyticAt ℂ (slice_fun f (fun i => (x i : ℂ)) v) w} :=
      isOpen_analyticAt ℂ (slice_fun f (fun i => (x i : ℂ)) v)
    rcases Metric.isOpen_iff.mp h_open 0 h_slice with ⟨ρ, hρ_pos, hρ_sub⟩
    let r := min (r_U / 2) (ρ / 2)
    have hr_pos : 0 < r := lt_min (half_pos hr_U_pos) (half_pos hρ_pos)
    have h_ball_U : Metric.ball x r ⊆ U := by
      intro y hy
      have h1 : dist y x < r_U := lt_of_lt_of_le (Metric.mem_ball.mp hy)
        ((min_le_left (r_U / 2) (ρ / 2)).trans (half_le_self hr_U_pos.le))
      exact hr_U_sub (Metric.mem_ball.mpr h1)
    have h_exists_loc := exists_local_analytic_extension_cauchy hn_le V_plus U hV_plus_open
      hV_plus_convex hV_plus_cone hV_plus_ne hU_open f h_cont h_holo_plus h_holo_minus x hx_U r
      hr_pos h_ball_U
    rcases h_exists_loc with ⟨F_x, hF_ana, hF_eq⟩
    exact ⟨F_x, r, hr_pos, hF_ana, hF_eq⟩

lemma eow_local_exists {n : ℕ} (hn_le : n ≤ 1) (V_plus U : Set (Fin n → ℝ))
    (hV_plus_open : IsOpen V_plus)
    (hV_plus_convex : Convex ℝ V_plus)
    (hV_plus_cone : ∀ v ∈ V_plus, ∀ (c : ℝ), c > 0 → (fun i => c * v i) ∈ V_plus)
    (hV_plus_ne : V_plus.Nonempty)
    (hU_open : IsOpen U)
    (f : (Fin n → ℂ) → ℂ)
    (h_cont : ContinuousOn f (WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U))
    (h_holo_plus : DifferentiableOn ℂ f (TubeDomain V_plus))
    (h_holo_minus : DifferentiableOn ℂ f (TubeDomain ((fun v : Fin n → ℝ => -v) '' V_plus)))
    (x : Fin n → ℝ) (hx_U : x ∈ U) :
    ∃ r_x > 0, Metric.ball x r_x ⊆ U ∧ ∃ F_x : (Fin n → ℂ) → ℂ,
      AnalyticOnNhd ℂ F_x (Metric.ball (fun i => (x i : ℂ)) r_x) ∧
      EqOn F_x f (Metric.ball (fun i => (x i : ℂ)) r_x ∩
        WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U) := by
  rcases eow_local_analytic_at hn_le V_plus U hV_plus_open hV_plus_convex hV_plus_cone hV_plus_ne
    hU_open f h_cont h_holo_plus h_holo_minus x hx_U with ⟨F_x, r_eq, hr_eq_pos, hF_ana, hF_eq⟩
  rcases exists_ball_subset_and_analyticOnNhd hU_open hx_U hF_ana with
    ⟨r_ball, hr_ball_pos, h_sub, h_ana_nhd⟩
  let r_x := min r_eq r_ball
  have hr_x_pos : 0 < r_x := lt_min hr_eq_pos hr_ball_pos
  refine ⟨r_x, hr_x_pos, (Metric.ball_subset_ball (min_le_right r_eq r_ball)).trans h_sub,
    F_x, ?_, ?_⟩
  · exact h_ana_nhd.mono (Metric.ball_subset_ball (min_le_right r_eq r_ball))
  · have h_ball_sub : Metric.ball (fun i => (x i : ℂ)) r_x ⊆
        Metric.ball (fun i => (x i : ℂ)) r_eq :=
      Metric.ball_subset_ball (min_le_left r_eq r_ball)
    exact hF_eq.mono (inter_subset_inter_left _ h_ball_sub)

lemma eow_nd_local_extension {n : ℕ} (hn_le : n ≤ 1) (V_plus U : Set (Fin n → ℝ))
    (hV_plus_open : IsOpen V_plus)
    (hV_plus_convex : Convex ℝ V_plus)
    (hV_plus_cone : ∀ v ∈ V_plus, ∀ (c : ℝ), c > 0 → (fun i => c * v i) ∈ V_plus)
    (hV_plus_ne : V_plus.Nonempty)
    (hU_open : IsOpen U)
    (f : (Fin n → ℂ) → ℂ)
    (h_cont : ContinuousOn f (WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U))
    (h_holo_plus : DifferentiableOn ℂ f (TubeDomain V_plus))
    (h_holo_minus : DifferentiableOn ℂ f (TubeDomain ((fun v : Fin n → ℝ => -v) '' V_plus))) :
    ∃ (r : (Fin n → ℝ) → ℝ) (_hr : ∀ x ∈ U, 0 < r x) (F_loc : (Fin n → ℝ) → (Fin n → ℂ) → ℂ),
      (∀ x ∈ U, DifferentiableOn ℂ (F_loc x) (Metric.ball (fun i => (x i : ℂ)) (r x))) ∧
      (∀ x ∈ U, EqOn (F_loc x) f (Metric.ball (fun i => (x i : ℂ)) (r x) ∩
        WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U)) ∧
      (∀ (x y : U), EqOn (F_loc x.1) (F_loc y.1)
        (Metric.ball (fun i => (x.1 i : ℂ)) (r x.1) ∩
          Metric.ball (fun i => (y.1 i : ℂ)) (r y.1))) := by
  have h_exists : ∀ x ∈ U, ∃ r_x > 0, Metric.ball x r_x ⊆ U ∧ ∃ F_x : (Fin n → ℂ) → ℂ,
      AnalyticOnNhd ℂ F_x (Metric.ball (fun i => (x i : ℂ)) r_x) ∧
      EqOn F_x f (Metric.ball (fun i => (x i : ℂ)) r_x ∩
        WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U) := by
    intro x hx
    exact eow_local_exists hn_le V_plus U hV_plus_open hV_plus_convex hV_plus_cone hV_plus_ne
      hU_open f h_cont h_holo_plus h_holo_minus x hx
  exact local_extension_assembly V_plus U f h_exists (eow_local_compat V_plus U f)

lemma differentiableOn_iUnion_of_locally_differentiable {ι : Type*} (s : ι → Set (Fin n → ℂ))
    (hs : ∀ i, IsOpen (s i)) (F_i : ι → (Fin n → ℂ) → ℂ)
    (h_diff : ∀ i, DifferentiableOn ℂ (F_i i) (s i))
    (h_compat : ∀ i j, EqOn (F_i i) (F_i j) (s i ∩ s j)) :
    ∃ F : (Fin n → ℂ) → ℂ,
      DifferentiableOn ℂ F (⋃ i, s i) ∧
      ∀ i, EqOn F (F_i i) (s i) := by
  classical
  let F : (Fin n → ℂ) → ℂ := fun z =>
    if h : ∃ i, z ∈ s i then F_i (Classical.choose h) z else 0
  have hF_eq : ∀ i, EqOn F (F_i i) (s i) := by
    intro i z hz
    have h : ∃ j, z ∈ s j := ⟨i, hz⟩
    dsimp [F]
    rw [dif_pos h]
    let j := Classical.choose h
    have hj : z ∈ s j := Classical.choose_spec h
    have hz_inter : z ∈ s j ∩ s i := ⟨hj, hz⟩
    exact h_compat j i hz_inter
  refine ⟨F, ?_, hF_eq⟩
  intro z hz
  simp only [mem_iUnion] at hz
  rcases hz with ⟨i, hi⟩
  have h_nhds : s i ∈ nhds z := (hs i).mem_nhds hi
  rw [← differentiableWithinAt_inter h_nhds]
  have h_sub : (⋃ j, s j) ∩ s i = s i := inter_eq_right.mpr (subset_iUnion s i)
  rw [h_sub]
  have h_diff_i : DifferentiableWithinAt ℂ (F_i i) (s i) z := h_diff i z hi
  exact DifferentiableWithinAt.congr h_diff_i (fun w hw => hF_eq i hw) (hF_eq i hi)

inductive WedgeCoverIdx (U : Set (Fin n → ℝ))
  | plus : WedgeCoverIdx U
  | minus : WedgeCoverIdx U
  | loc (x : U) : WedgeCoverIdx U

def coverSet (V_plus : Set (Fin n → ℝ)) (U : Set (Fin n → ℝ))
    (r : (Fin n → ℝ) → ℝ) : WedgeCoverIdx U → Set (Fin n → ℂ)
  | .plus => TubeDomain V_plus
  | .minus => TubeDomain ((fun v => -v) '' V_plus)
  | .loc ⟨x, _hx⟩ => Metric.ball (fun i => (x i : ℂ)) (r x)

def coverFun (U : Set (Fin n → ℝ)) (f : (Fin n → ℂ) → ℂ)
    (F_loc : (Fin n → ℝ) → (Fin n → ℂ) → ℂ) :
    WedgeCoverIdx U → (Fin n → ℂ) → ℂ
  | .plus => f
  | .minus => f
  | .loc ⟨x, _hx⟩ => F_loc x

lemma iUnion_coverSet (V_plus : Set (Fin n → ℝ)) (U : Set (Fin n → ℝ))
    (r : (Fin n → ℝ) → ℝ) :
    (⋃ i, coverSet V_plus U r i) =
    TubeDomain V_plus ∪ TubeDomain ((fun v => -v) '' V_plus) ∪
      ⋃ x ∈ U, Metric.ball (fun i => (x i : ℂ)) (r x) := by
  ext z
  simp only [mem_iUnion, mem_union]
  constructor
  · rintro ⟨i, hi⟩
    cases i with
    | plus => left; left; exact hi
    | minus => left; right; exact hi
    | loc x => right; exact ⟨x.1, x.2, hi⟩
  · rintro ((h | h) | ⟨x, hx, h⟩)
    · exact ⟨.plus, h⟩
    · exact ⟨.minus, h⟩
    · exact ⟨.loc ⟨x, hx⟩, h⟩

lemma eow_nd_compat (V_plus U : Set (Fin n → ℝ))
    (f : (Fin n → ℂ) → ℂ)
    (r : (Fin n → ℝ) → ℝ)
    (F_loc : (Fin n → ℝ) → (Fin n → ℂ) → ℂ)
    (hF_eq : ∀ x ∈ U, EqOn (F_loc x) f (Metric.ball (fun i => (x i : ℂ)) (r x) ∩
      WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U))
    (hF_compat : ∀ (x y : U), EqOn (F_loc x.1) (F_loc y.1)
      (Metric.ball (fun i => (x.1 i : ℂ)) (r x.1) ∩ Metric.ball (fun i => (y.1 i : ℂ)) (r y.1))) :
    ∀ i j : WedgeCoverIdx U, EqOn (coverFun U f F_loc i) (coverFun U f F_loc j)
      (coverSet V_plus U r i ∩ coverSet V_plus U r j) := by
  intro i j z hz
  cases i with
  | plus =>
    cases j with
    | plus => rfl
    | minus => rfl
    | loc x =>
      rcases x with ⟨x, hx⟩
      have hz_loc : z ∈ Metric.ball (fun i => (x i : ℂ)) (r x) := hz.2
      have hz_plus : z ∈ TubeDomain V_plus := hz.1
      have hz_wedge : z ∈ WedgeDomain V_plus ((fun v => -v) '' V_plus) U := by
        left; left; exact hz_plus
      have h := hF_eq x hx ⟨hz_loc, hz_wedge⟩
      exact h.symm
  | minus =>
    cases j with
    | plus => rfl
    | minus => rfl
    | loc x =>
      rcases x with ⟨x, hx⟩
      have hz_loc : z ∈ Metric.ball (fun i => (x i : ℂ)) (r x) := hz.2
      have hz_minus : z ∈ TubeDomain ((fun v => -v) '' V_plus) := hz.1
      have hz_wedge : z ∈ WedgeDomain V_plus ((fun v => -v) '' V_plus) U := by
        left; right; exact hz_minus
      have h := hF_eq x hx ⟨hz_loc, hz_wedge⟩
      exact h.symm
  | loc x =>
    cases j with
    | plus =>
      rcases x with ⟨x, hx⟩
      have hz_loc : z ∈ Metric.ball (fun i => (x i : ℂ)) (r x) := hz.1
      have hz_plus : z ∈ TubeDomain V_plus := hz.2
      have hz_wedge : z ∈ WedgeDomain V_plus ((fun v => -v) '' V_plus) U := by
        left; left; exact hz_plus
      exact hF_eq x hx ⟨hz_loc, hz_wedge⟩
    | minus =>
      rcases x with ⟨x, hx⟩
      have hz_loc : z ∈ Metric.ball (fun i => (x i : ℂ)) (r x) := hz.1
      have hz_minus : z ∈ TubeDomain ((fun v => -v) '' V_plus) := hz.2
      have hz_wedge : z ∈ WedgeDomain V_plus ((fun v => -v) '' V_plus) U := by
        left; right; exact hz_minus
      exact hF_eq x hx ⟨hz_loc, hz_wedge⟩
    | loc y =>
      exact hF_compat x y hz

lemma eow_nd_glue (V_plus U : Set (Fin n → ℝ))
    (hV_plus_open : IsOpen V_plus)
    (_hV_plus_cone : ∀ v ∈ V_plus, ∀ (c : ℝ), c > 0 → (fun i => c * v i) ∈ V_plus)
    (_hU_open : IsOpen U)
    (f : (Fin n → ℂ) → ℂ)
    (_h_cont : ContinuousOn f (WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U))
    (h_holo_plus : DifferentiableOn ℂ f (TubeDomain V_plus))
    (h_holo_minus : DifferentiableOn ℂ f (TubeDomain ((fun v : Fin n → ℝ => -v) '' V_plus)))
    (r : (Fin n → ℝ) → ℝ) (hr : ∀ x ∈ U, 0 < r x)
    (F_loc : (Fin n → ℝ) → (Fin n → ℂ) → ℂ)
    (hF_holo : ∀ x ∈ U, DifferentiableOn ℂ (F_loc x) (Metric.ball (fun i => (x i : ℂ)) (r x)))
    (hF_eq : ∀ x ∈ U, EqOn (F_loc x) f (Metric.ball (fun i => (x i : ℂ)) (r x) ∩
      WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U))
    (hF_compat : ∀ (x y : U), EqOn (F_loc x.1) (F_loc y.1)
      (Metric.ball (fun i => (x.1 i : ℂ)) (r x.1) ∩ Metric.ball (fun i => (y.1 i : ℂ)) (r y.1))) :
    ∃ F : (Fin n → ℂ) → ℂ,
      DifferentiableOn ℂ F (TubeDomain V_plus ∪ TubeDomain ((fun v : Fin n → ℝ => -v) '' V_plus) ∪
        ⋃ x ∈ U, Metric.ball (fun i => (x i : ℂ)) (r x)) ∧
      EqOn F f (WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U) := by
  have hs_open : ∀ i : WedgeCoverIdx U, IsOpen (coverSet V_plus U r i) := by
    intro i
    cases i with
    | plus => exact isOpen_TubeDomain hV_plus_open
    | minus => exact isOpen_TubeDomain_minus V_plus hV_plus_open
    | loc x => exact Metric.isOpen_ball
  have h_diff : ∀ i : WedgeCoverIdx U,
      DifferentiableOn ℂ (coverFun U f F_loc i) (coverSet V_plus U r i) := by
    intro i
    cases i with
    | plus => exact h_holo_plus
    | minus => exact h_holo_minus
    | loc x => exact hF_holo x.1 x.2
  have h_compat : ∀ i j : WedgeCoverIdx U, EqOn (coverFun U f F_loc i) (coverFun U f F_loc j)
      (coverSet V_plus U r i ∩ coverSet V_plus U r j) :=
    eow_nd_compat V_plus U f r F_loc hF_eq hF_compat
  rcases differentiableOn_iUnion_of_locally_differentiable (coverSet V_plus U r) hs_open
    (coverFun U f F_loc) h_diff h_compat with ⟨F, hF_diff, hF_eq_i⟩
  rw [iUnion_coverSet] at hF_diff
  refine ⟨F, hF_diff, ?_⟩
  intro z hz
  simp only [WedgeDomain, mem_union, mem_setOf_eq] at hz
  rcases hz with ((h_plus | h_minus) | ⟨hx_re, hx_im⟩)
  · exact hF_eq_i .plus h_plus
  · exact hF_eq_i .minus h_minus
  · let x : Fin n → ℝ := fun i => (z i).re
    have hx_U : x ∈ U := hx_re
    have hx_eq : z = fun i => (x i : ℂ) := by
      ext i
      have h_im : (z i).im = 0 := congr_fun hx_im i
      exact Complex.ext rfl (by simp [x, h_im])
    have hz_ball : z ∈ coverSet V_plus U r (.loc ⟨x, hx_U⟩) := by
      dsimp [coverSet]
      rw [hx_eq]
      exact Metric.mem_ball_self (hr x hx_U)
    have h1 := hF_eq_i (.loc ⟨x, hx_U⟩) hz_ball
    have h2 := hF_eq x hx_U ⟨hz_ball, by
      simp only [WedgeDomain, mem_union, mem_setOf_eq]
      right; exact ⟨hx_re, hx_im⟩⟩
    exact h1.trans h2

lemma eow_nd_continuation {n : ℕ} (hn_le : n ≤ 1) (V_plus U : Set (Fin n → ℝ))
    (hV_plus_open : IsOpen V_plus)
    (hV_plus_convex : Convex ℝ V_plus)
    (hV_plus_cone : ∀ v ∈ V_plus, ∀ (c : ℝ), c > 0 → (fun i => c * v i) ∈ V_plus)
    (hV_plus_ne : V_plus.Nonempty)
    (hU_open : IsOpen U)
    (f : (Fin n → ℂ) → ℂ)
    (h_cont : ContinuousOn f (WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U))
    (h_holo_plus : DifferentiableOn ℂ f (TubeDomain V_plus))
    (h_holo_minus : DifferentiableOn ℂ f (TubeDomain ((fun v : Fin n → ℝ => -v) '' V_plus))) :
    ∃ W : Set (Fin n → ℂ), IsOpen W ∧
      (WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U) ⊆ W ∧
      ∃ F : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ F W ∧
      EqOn F f (WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U) := by
  rcases eow_nd_local_extension hn_le V_plus U hV_plus_open hV_plus_convex hV_plus_cone hV_plus_ne
    hU_open f h_cont h_holo_plus h_holo_minus with
    ⟨r, hr, F_loc, hF_holo, hF_eq, hF_compat⟩
  let W : Set (Fin n → ℂ) :=
    TubeDomain V_plus ∪ TubeDomain ((fun v : Fin n → ℝ => -v) '' V_plus) ∪
    ⋃ x ∈ U, Metric.ball (fun i => (x i : ℂ)) (r x)
  have hW_open : IsOpen W := isOpen_wedge_neighborhood V_plus U hV_plus_open r
  have hW_sub : WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U ⊆ W :=
    wedge_subset_union_balls V_plus U r hr
  refine ⟨W, hW_open, hW_sub, ?_⟩
  exact eow_nd_glue V_plus U hV_plus_open hV_plus_cone hU_open f h_cont
    h_holo_plus h_holo_minus r hr F_loc hF_holo hF_eq hF_compat

theorem eow_nd {n : ℕ} (hn_le : n ≤ 1) (V_plus U : Set (Fin n → ℝ))
    (hV_plus_open : IsOpen V_plus)
    (hV_plus_convex : Convex ℝ V_plus)
    (hV_plus_cone : ∀ v ∈ V_plus, ∀ (c : ℝ), c > 0 → (fun i => c * v i) ∈ V_plus)
    (hV_plus_ne : V_plus.Nonempty)
    (hU_open : IsOpen U)
    (f : (Fin n → ℂ) → ℂ)
    (h_cont : ContinuousOn f (WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U))
    (h_holo_plus : DifferentiableOn ℂ f (TubeDomain V_plus))
    (h_holo_minus : DifferentiableOn ℂ f (TubeDomain ((fun v : Fin n → ℝ => -v) '' V_plus))) :
    ∃ W : Set (Fin n → ℂ), IsOpen W ∧
      (WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U) ⊆ W ∧
      ∃ F : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ F W ∧
      EqOn F f (WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U) := by
  exact eow_nd_continuation hn_le V_plus U hV_plus_open hV_plus_convex hV_plus_cone hV_plus_ne
    hU_open f h_cont h_holo_plus h_holo_minus

open Analysis

def consFin {k : ℕ} (w' : Fin k → ℂ) (wk : ℂ) : Fin (k + 1) → ℂ :=
  Fin.snoc w' wk

def initFin {k : ℕ} (w : Fin (k + 1) → ℂ) : Fin k → ℂ :=
  fun i => w (Fin.castSucc i)

def lastFin {k : ℕ} (w : Fin (k + 1) → ℂ) : ℂ :=
  w (Fin.last k)

def lastFinR {k : ℕ} (r : Fin (k + 1) → ℝ) : ℝ :=
  r (Fin.last k)

def initFinR {k : ℕ} (r : Fin (k + 1) → ℝ) : Fin k → ℝ :=
  fun i => r (Fin.castSucc i)

lemma consFin_init_last {k : ℕ} (w : Fin (k + 1) → ℂ) :
    consFin (initFin w) (lastFin w) = w := by
  ext i
  dsimp [consFin, initFin, lastFin]
  refine Fin.lastCases ?_ ?_ i
  · rw [Fin.snoc_last]
  · intro j
    rw [Fin.snoc_castSucc]
    rfl

lemma initFin_consFin {k : ℕ} (w' : Fin k → ℂ) (wk : ℂ) :
    initFin (consFin w' wk) = w' := by
  ext i
  dsimp [initFin, consFin]
  rw [Fin.snoc_castSucc]

lemma lastFin_consFin {k : ℕ} (w' : Fin k → ℂ) (wk : ℂ) :
    lastFin (consFin w' wk) = wk := by
  dsimp [lastFin, consFin]
  rw [Fin.snoc_last]

lemma continuous_initFin {k : ℕ} :
    Continuous (initFin (k := k)) := by
  apply continuous_pi
  intro i
  exact continuous_apply (Fin.castSucc i)

lemma continuous_lastFin {k : ℕ} :
    Continuous (lastFin (k := k)) :=
  continuous_apply (Fin.last k)

lemma continuous_consFin {k : ℕ} :
    Continuous (fun (p : (Fin k → ℂ) × ℂ) => consFin p.1 p.2) := by
  apply continuous_pi
  intro i
  refine Fin.lastCases ?_ ?_ i
  · have h : (fun (p : (Fin k → ℂ) × ℂ) => consFin p.1 p.2 (Fin.last k)) = Prod.snd := by
      ext p; dsimp [consFin]; rw [Fin.snoc_last]
    rw [h]
    exact continuous_snd
  · intro j
    have h : (fun (p : (Fin k → ℂ) × ℂ) => consFin p.1 p.2 (Fin.castSucc j)) =
        (fun p => p.1 j) := by
      ext p; dsimp [consFin]; rw [Fin.snoc_castSucc]
    rw [h]
    exact (continuous_apply j).comp continuous_fst

lemma consFin_mem_pos_orthant_iff {k : ℕ} (w : Fin (k + 1) → ℂ) :
    w ∈ TubeDomain (PosOrthant (k + 1)) ↔
      initFin w ∈ TubeDomain (PosOrthant k) ∧ 0 < (lastFin w).im := by
  constructor
  · intro hw
    refine ⟨fun i => hw (Fin.castSucc i), hw (Fin.last k)⟩
  · intro ⟨hw', hwk⟩ j
    refine Fin.lastCases ?_ ?_ j
    · exact hwk
    · intro i
      exact hw' i

lemma consFin_mem_neg_orthant_iff {k : ℕ} (w : Fin (k + 1) → ℂ) :
    w ∈ TubeDomain (NegOrthant (k + 1)) ↔
      initFin w ∈ TubeDomain (NegOrthant k) ∧ (lastFin w).im < 0 := by
  constructor
  · intro hw
    refine ⟨fun i => hw (Fin.castSucc i), hw (Fin.last k)⟩
  · intro ⟨hw', hwk⟩ j
    refine Fin.lastCases ?_ ?_ j
    · exact hwk
    · intro i
      exact hw' i

lemma consFin_mem_ball {k : ℕ} {r : ℝ} (hr : 0 < r)
    {w' : Fin k → ℂ} (hw' : w' ∈ Metric.ball (0 : Fin k → ℂ) r)
    {wk : ℂ} (hwk : wk ∈ Metric.ball (0 : ℂ) r) :
    consFin w' wk ∈ Metric.ball (0 : Fin (k + 1) → ℂ) r := by
  rw [Metric.mem_ball]
  apply (dist_pi_lt_iff hr).mpr
  intro i
  refine Fin.lastCases ?_ ?_ i
  · dsimp [consFin]
    rw [Fin.snoc_last]
    exact Metric.mem_ball.mp hwk
  · intro j
    have hj : consFin w' wk (Fin.castSucc j) = w' j := by
      dsimp [consFin]; rw [Fin.snoc_castSucc]
    rw [hj]
    exact (dist_le_pi_dist w' 0 j).trans_lt (Metric.mem_ball.mp hw')

lemma initFin_mem_ball {k : ℕ} {r : ℝ}
    {w : Fin (k + 1) → ℂ} (hw : w ∈ Metric.ball (0 : Fin (k + 1) → ℂ) r) :
    initFin w ∈ Metric.ball (0 : Fin k → ℂ) r := by
  rw [Metric.mem_ball] at hw ⊢
  apply (dist_pi_lt_iff (lt_of_le_of_lt dist_nonneg hw)).mpr
  intro i
  dsimp [initFin]
  exact (dist_le_pi_dist w 0 (Fin.castSucc i)).trans_lt hw

lemma lastFin_mem_ball {k : ℕ} {r : ℝ}
    {w : Fin (k + 1) → ℂ} (hw : w ∈ Metric.ball (0 : Fin (k + 1) → ℂ) r) :
    lastFin w ∈ Metric.ball (0 : ℂ) r := by
  rw [Metric.mem_ball] at hw ⊢
  dsimp [lastFin]
  exact (dist_le_pi_dist w 0 (Fin.last k)).trans_lt hw

def prodOpenSet {k : ℕ} (W' : Set (Fin k → ℂ)) (D : Set ℂ) : Set (Fin (k + 1) → ℂ) :=
  initFin ⁻¹' W' ∩ lastFin ⁻¹' D

lemma isOpen_prodOpenSet {k : ℕ} {W' : Set (Fin k → ℂ)} (hW' : IsOpen W')
    {D : Set ℂ} (hD : IsOpen D) :
    IsOpen (prodOpenSet W' D) :=
  (hW'.preimage continuous_initFin).inter (hD.preimage continuous_lastFin)

lemma nonempty_prodOpenSet {k : ℕ} {W' : Set (Fin k → ℂ)} (hW' : W'.Nonempty)
    {D : Set ℂ} (hD : D.Nonempty) :
    (prodOpenSet W' D).Nonempty := by
  rcases hW' with ⟨w', hw'⟩
  rcases hD with ⟨z, hz⟩
  refine ⟨consFin w' z, ?_⟩
  dsimp [prodOpenSet]
  rw [mem_inter_iff, mem_preimage, mem_preimage, initFin_consFin, lastFin_consFin]
  exact ⟨hw', hz⟩

lemma prodOpenSet_subset_pos_orthant {k : ℕ}
    {W' : Set (Fin k → ℂ)} (hW' : W' ⊆ TubeDomain (PosOrthant k))
    {D : Set ℂ} (hD : D ⊆ {z : ℂ | 0 < z.im}) :
    prodOpenSet W' D ⊆ TubeDomain (PosOrthant (k + 1)) := by
  intro w hw
  dsimp [prodOpenSet] at hw
  rw [mem_inter_iff, mem_preimage, mem_preimage] at hw
  have hw' := hW' hw.1
  have hwk := hD hw.2
  exact (consFin_mem_pos_orthant_iff w).mpr ⟨hw', hwk⟩

lemma prodOpenSet_subset_neg_orthant {k : ℕ}
    {W' : Set (Fin k → ℂ)} (hW' : W' ⊆ TubeDomain (NegOrthant k))
    {D : Set ℂ} (hD : D ⊆ {z : ℂ | z.im < 0}) :
    prodOpenSet W' D ⊆ TubeDomain (NegOrthant (k + 1)) := by
  intro w hw
  dsimp [prodOpenSet] at hw
  rw [mem_inter_iff, mem_preimage, mem_preimage] at hw
  have hw' := hW' hw.1
  have hwk := hD hw.2
  exact (consFin_mem_neg_orthant_iff w).mpr ⟨hw', hwk⟩

lemma prodOpenSet_subset_ball {k : ℕ} {r : ℝ} (hr : 0 < r)
    {W' : Set (Fin k → ℂ)} (hW' : W' ⊆ Metric.ball 0 r)
    {D : Set ℂ} (hD : D ⊆ Metric.ball 0 r) :
    prodOpenSet W' D ⊆ Metric.ball 0 r := by
  intro w hw
  dsimp [prodOpenSet] at hw
  rw [mem_inter_iff, mem_preimage, mem_preimage] at hw
  have hw' := hW' hw.1
  have hwk := hD hw.2
  have heq : w = consFin (initFin w) (lastFin w) := (consFin_init_last w).symm
  rw [heq]
  exact consFin_mem_ball hr hw' hwk

noncomputable def iteratedCauchyIntegral2
    (g : (Fin 2 → ℂ) → ℂ) (c : Fin 2 → ℂ) (r : Fin 2 → ℝ) (w : Fin 2 → ℂ) : ℂ :=
  (2 * Real.pi * Complex.I : ℂ)⁻¹ • ∮ ζ₀ in C(c 0, r 0), (ζ₀ - w 0)⁻¹ •
    ((2 * Real.pi * Complex.I : ℂ)⁻¹ • ∮ ζ₁ in C(c 1, r 1), (ζ₁ - w 1)⁻¹ •
      g (fun i => if i = 0 then ζ₀ else ζ₁))

noncomputable def cauchySlice1
    (g : (Fin 2 → ℂ) → ℂ) (c1 : ℂ) (r1 : ℝ) (ζ₀ : ℂ) (w1 : ℂ) : ℂ :=
  (2 * Real.pi * Complex.I : ℂ)⁻¹ • ∮ ζ₁ in C(c1, r1), (ζ₁ - w1)⁻¹ •
    g (fun i => if i = 0 then ζ₀ else ζ₁)

lemma analyticAt_cauchySlice1
    (g : (Fin 2 → ℂ) → ℂ) (c1 : ℂ) (r1 : ℝ) (hr1 : 0 < r1) (ζ₀ : ℂ)
    (h_int : CircleIntegrable (fun ζ₁ => g (fun i => if i = 0 then ζ₀ else ζ₁)) c1 r1)
    {w1 : ℂ} (hw1 : w1 ∈ Metric.ball c1 r1) :
    AnalyticAt ℂ (fun u => cauchySlice1 g c1 r1 ζ₀ u) w1 := by
  dsimp [cauchySlice1]
  lift r1 to NNReal using hr1.le with R1
  have hw' : w1 ∈ Metric.eball c1 R1 := by
    rw [Metric.eball_coe]
    exact hw1
  have h_series := hasFPowerSeriesOn_cauchy_integral h_int hr1
  exact h_series.analyticAt_of_mem hw'

lemma analyticAt_iteratedCauchyIntegral2_slice0
    (g : (Fin 2 → ℂ) → ℂ) (c : Fin 2 → ℂ) (r : Fin 2 → ℝ) (hr0 : 0 < r 0)
    (w1 : ℂ)
    (h_int : CircleIntegrable (fun ζ₀ => cauchySlice1 g (c 1) (r 1) ζ₀ w1) (c 0) (r 0))
    {w0 : ℂ} (hw0 : w0 ∈ Metric.ball (c 0) (r 0)) :
    AnalyticAt ℂ (fun u => (2 * Real.pi * Complex.I : ℂ)⁻¹ •
      ∮ ζ₀ in C(c 0, r 0), (ζ₀ - u)⁻¹ • cauchySlice1 g (c 1) (r 1) ζ₀ w1) w0 := by
  lift (r 0) to NNReal using hr0.le with R0
  have hw' : w0 ∈ Metric.eball (c 0) R0 := by
    rw [Metric.eball_coe]
    exact hw0
  have h_series := hasFPowerSeriesOn_cauchy_integral h_int hr0
  exact h_series.analyticAt_of_mem hw'

lemma iteratedCauchyIntegral2_eq
    (g : (Fin 2 → ℂ) → ℂ) (c : Fin 2 → ℂ) (r : Fin 2 → ℝ)
    (hr0 : 0 < r 0) (_hr1 : 0 < r 1)
    (w : Fin 2 → ℂ)
    (hw0 : w 0 ∈ Metric.ball (c 0) (r 0))
    (hw1 : w 1 ∈ Metric.ball (c 1) (r 1))
    (h_diff1 : ∀ ζ₀ ∈ Metric.sphere (c 0) (r 0),
      DifferentiableOn ℂ (fun ζ₁ => g (fun i => if i = 0 then ζ₀ else ζ₁))
        (Metric.closedBall (c 1) (r 1)))
    (h_diff0 : DifferentiableOn ℂ (fun ζ₀ => g (fun i => if i = 0 then ζ₀ else w 1))
        (Metric.closedBall (c 0) (r 0))) :
    iteratedCauchyIntegral2 g c r w = g w := by
  have h_inner_eq : ∀ ζ₀ ∈ Metric.sphere (c 0) (r 0),
      ((2 * ↑Real.pi * Complex.I : ℂ)⁻¹ • ∮ ζ₁ in C(c 1, r 1), (ζ₁ - w 1)⁻¹ •
        g (fun i => if i = 0 then ζ₀ else ζ₁)) =
      g (fun i => if i = 0 then ζ₀ else w 1) := by
    intro ζ₀ hζ₀
    have h_diff := h_diff1 ζ₀ hζ₀
    have h_cauchy := DifferentiableOn.circleIntegral_sub_inv_smul h_diff hw1
    have h_2piI_ne : (2 * ↑Real.pi * Complex.I : ℂ) ≠ 0 := by
      simp [Complex.I_ne_zero, Real.pi_ne_zero]
    calc (2 * ↑Real.pi * Complex.I : ℂ)⁻¹ • ∮ ζ₁ in C(c 1, r 1), (ζ₁ - w 1)⁻¹ •
            g (fun i => if i = 0 then ζ₀ else ζ₁)
      _ = (2 * ↑Real.pi * Complex.I : ℂ)⁻¹ • ((2 * ↑Real.pi * Complex.I : ℂ) •
            (fun ζ₁ => g (fun i => if i = 0 then ζ₀ else ζ₁)) (w 1)) := by rw [← h_cauchy]
      _ = (fun ζ₁ => g (fun i => if i = 0 then ζ₀ else ζ₁)) (w 1) := by
        rw [← mul_smul, inv_mul_cancel₀ h_2piI_ne, one_smul]
      _ = g (fun i => if i = 0 then ζ₀ else w 1) := rfl
  have h_int_congr : (∮ ζ₀ in C(c 0, r 0), (ζ₀ - w 0)⁻¹ •
        ((2 * ↑Real.pi * Complex.I : ℂ)⁻¹ • ∮ ζ₁ in C(c 1, r 1), (ζ₁ - w 1)⁻¹ •
          g (fun i => if i = 0 then ζ₀ else ζ₁))) =
      ∮ ζ₀ in C(c 0, r 0), (ζ₀ - w 0)⁻¹ • g (fun i => if i = 0 then ζ₀ else w 1) := by
    apply circleIntegral.integral_congr hr0.le
    intro ζ₀ hζ₀
    dsimp only
    rw [h_inner_eq ζ₀ hζ₀]
  have h_cauchy0 := DifferentiableOn.circleIntegral_sub_inv_smul h_diff0 hw0
  have h_2piI_ne : (2 * ↑Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Complex.I_ne_zero, Real.pi_ne_zero]
  unfold iteratedCauchyIntegral2
  rw [h_int_congr]
  calc (2 * ↑Real.pi * Complex.I : ℂ)⁻¹ • ∮ ζ₀ in C(c 0, r 0), (ζ₀ - w 0)⁻¹ •
          g (fun i => if i = 0 then ζ₀ else w 1)
    _ = (2 * ↑Real.pi * Complex.I : ℂ)⁻¹ • ((2 * ↑Real.pi * Complex.I : ℂ) •
          (fun ζ₀ => g (fun i => if i = 0 then ζ₀ else w 1)) (w 0)) := by rw [← h_cauchy0]
    _ = (fun ζ₀ => g (fun i => if i = 0 then ζ₀ else w 1)) (w 0) := by
      rw [← mul_smul, inv_mul_cancel₀ h_2piI_ne, one_smul]
    _ = g w := by
      have heq : (fun i : Fin 2 => if i = 0 then w 0 else w 1) = w := by
        ext i; fin_cases i <;> rfl
      exact congr_arg g heq

lemma analyticAt_inv_sub {ζ w : ℂ} (h : ζ ≠ w) :
    AnalyticAt ℂ (fun u => (ζ - u)⁻¹) w := by
  have h_sub : AnalyticAt ℂ (fun u => ζ - u) w :=
    analyticAt_const.sub analyticAt_id
  have h_ne : ζ - w ≠ 0 := sub_ne_zero.mpr h
  exact h_sub.inv h_ne

lemma analyticAt_cauchy_kernel_proj0 {ζ₀ : ℂ} {w : Fin 2 → ℂ} (h : ζ₀ ≠ w 0) :
    AnalyticAt ℂ (fun u : Fin 2 → ℂ => (ζ₀ - u 0)⁻¹) w := by
  let P : (Fin 2 → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj 0
  have hP : AnalyticAt ℂ P w := P.analyticAt w
  have h1 : AnalyticAt ℂ (fun u => (ζ₀ - u)⁻¹) (P w) := analyticAt_inv_sub h
  exact h1.comp hP

lemma analyticAt_cauchy_kernel_proj1 {ζ₁ : ℂ} {w : Fin 2 → ℂ} (h : ζ₁ ≠ w 1) :
    AnalyticAt ℂ (fun u : Fin 2 → ℂ => (ζ₁ - u 1)⁻¹) w := by
  let P : (Fin 2 → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj 1
  have hP : AnalyticAt ℂ P w := P.analyticAt w
  have h1 : AnalyticAt ℂ (fun u => (ζ₁ - u)⁻¹) (P w) := analyticAt_inv_sub h
  exact h1.comp hP

lemma analyticAt_cauchy_kernel_prod {ζ₀ ζ₁ : ℂ} {w : Fin 2 → ℂ}
    (h0 : ζ₀ ≠ w 0) (h1 : ζ₁ ≠ w 1) :
    AnalyticAt ℂ (fun u : Fin 2 → ℂ => (ζ₀ - u 0)⁻¹ * (ζ₁ - u 1)⁻¹) w :=
  (analyticAt_cauchy_kernel_proj0 h0).mul (analyticAt_cauchy_kernel_proj1 h1)

noncomputable def iteratedCauchy (k : ℕ) (g : (Fin k → ℂ) → ℂ)
    (c : Fin k → ℂ) (r : Fin k → ℝ) (w : Fin k → ℂ) : ℂ :=
  match k with
  | 0 => g w
  | m + 1 =>
    (2 * Real.pi * Complex.I : ℂ)⁻¹ • ∮ ζ in C(lastFin c, lastFinR r),
      (ζ - lastFin w)⁻¹ •
        iteratedCauchy m (fun w' => g (consFin w' ζ)) (initFin c) (initFinR r) (initFin w)

lemma iteratedCauchy_zero (g : (Fin 0 → ℂ) → ℂ) (c : Fin 0 → ℂ) (r : Fin 0 → ℝ) (w : Fin 0 → ℂ) :
    iteratedCauchy 0 g c r w = g w := rfl

lemma continuous_deriv_circleMap' (c : ℂ) (R : ℝ) :
    Continuous (deriv (circleMap c R)) := by
  have heq : (deriv (circleMap c R)) = fun θ : ℝ => circleMap 0 R θ * I := by
    ext θ
    exact deriv_circleMap c R θ
  rw [heq]
  exact (continuous_circleMap 0 R).mul continuous_const

lemma tendsto_circleIntegral_cauchy_of_dominated
    {c : ℂ} {R : ℝ} (hR : 0 < R)
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (F_eps : ι → ℂ → ℂ) (F_lim : ℂ → ℂ)
    (h_cont : ∀ᶠ n in l, ContinuousOn (F_eps n) (Metric.sphere c R))
    (M : ℝ) (hM : ∀ᶠ n in l, ∀ z ∈ Metric.sphere c R, ‖F_eps n z‖ ≤ M)
    (h_pt : ∀ z ∈ Metric.sphere c R, Filter.Tendsto (fun n => F_eps n z) l (nhds (F_lim z)))
    {w : ℂ} (hw : w ∈ Metric.ball c R) :
    Filter.Tendsto
      (fun n => (2 * Real.pi * Complex.I : ℂ)⁻¹ • ∮ ζ in C(c, R), (ζ - w)⁻¹ • F_eps n ζ) l
      (nhds ((2 * Real.pi * Complex.I : ℂ)⁻¹ • ∮ ζ in C(c, R), (ζ - w)⁻¹ • F_lim ζ)) := by
  have h_2piI : Continuous (fun (I_val : ℂ) => (2 * ↑Real.pi * Complex.I : ℂ)⁻¹ • I_val) := by
    fun_prop
  apply h_2piI.continuousAt.tendsto.comp
  change Filter.Tendsto
    (fun n => ∫ θ in (0:ℝ)..(2 * Real.pi),
      deriv (circleMap c R) θ • ((circleMap c R θ - w)⁻¹ • F_eps n (circleMap c R θ))) l
    (nhds (∫ θ in (0:ℝ)..(2 * Real.pi),
      deriv (circleMap c R) θ • ((circleMap c R θ - w)⁻¹ • F_lim (circleMap c R θ))))
  have hd_pos : 0 < R - dist w c := sub_pos.mpr (Metric.mem_ball.mp hw)
  let bound : ℝ → ℝ := fun _ => R * (R - dist w c)⁻¹ * max M 0
  have h_bound_int : IntervalIntegrable bound MeasureTheory.volume 0 (2 * Real.pi) :=
    intervalIntegrable_const
  have h_cm_sphere : ∀ θ : ℝ, circleMap c R θ ∈ Metric.sphere c R := by
    intro θ
    rw [Metric.mem_sphere, circleMap, dist_eq_norm, add_sub_cancel_left, norm_mul,
      Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_of_nonneg hR.le]
  have h_diff_ne : ∀ θ : ℝ, circleMap c R θ - w ≠ 0 := by
    intro θ h_sub
    have heq : circleMap c R θ = w := sub_eq_zero.mp h_sub
    have h_dist1 : dist (circleMap c R θ) c = R := by
      have := h_cm_sphere θ
      rwa [Metric.mem_sphere] at this
    rw [heq] at h_dist1
    have h_dist2 : dist w c < R := Metric.mem_ball.mp hw
    linarith
  have h_inv_le : ∀ θ : ℝ, ‖(circleMap c R θ - w)⁻¹‖ ≤ (R - dist w c)⁻¹ := by
    intro θ
    rw [norm_inv]
    have h1 : dist (circleMap c R θ) c ≤ dist (circleMap c R θ) w + dist w c := dist_triangle _ _ _
    have h2 : dist (circleMap c R θ) c = R := by
      have := h_cm_sphere θ
      rwa [Metric.mem_sphere] at this
    rw [h2] at h1
    have h_norm : dist (circleMap c R θ) w = ‖circleMap c R θ - w‖ := dist_eq_norm _ _
    rw [h_norm, dist_comm w c] at h1
    have h_le : R - dist c w ≤ ‖circleMap c R θ - w‖ := by linarith
    rw [dist_comm c w] at h_le
    have h_norm_pos : 0 < ‖circleMap c R θ - w‖ := by
      rw [norm_pos_iff]
      exact h_diff_ne θ
    exact (inv_le_inv₀ h_norm_pos hd_pos).mpr h_le
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence bound
  · filter_upwards [h_cont] with n hn
    have h_cont_on : Continuous (fun θ =>
        deriv (circleMap c R) θ • ((circleMap c R θ - w)⁻¹ • F_eps n (circleMap c R θ))) := by
      have h_cm_cont : Continuous (circleMap c R) := continuous_circleMap c R
      have h_der_cont : Continuous (deriv (circleMap c R)) := continuous_deriv_circleMap' c R
      have h_inv_cont : Continuous (fun θ => (circleMap c R θ - w)⁻¹) := by
        exact (h_cm_cont.sub continuous_const).inv₀ h_diff_ne
      have h_F_cont : Continuous (fun θ => F_eps n (circleMap c R θ)) :=
        hn.comp_continuous h_cm_cont h_cm_sphere
      exact h_der_cont.smul (h_inv_cont.smul h_F_cont)
    exact h_cont_on.aestronglyMeasurable
  · filter_upwards [hM] with n hMn
    refine ae_of_all _ ?_
    intro θ _hθ
    dsimp [bound]
    rw [norm_mul, norm_mul]
    have h_deriv_norm : ‖deriv (circleMap c R) θ‖ = R := by
      rw [deriv_circleMap, norm_mul, Complex.norm_I, mul_one, circleMap,
        zero_add, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
        Real.norm_of_nonneg hR.le]
    rw [h_deriv_norm]
    have h_fn_le : ‖F_eps n (circleMap c R θ)‖ ≤ max M 0 :=
      (hMn _ (h_cm_sphere θ)).trans (le_max_left _ _)
    have h_mul1 : R * ‖(circleMap c R θ - w)⁻¹‖ ≤ R * (R - dist w c)⁻¹ :=
      mul_le_mul_of_nonneg_left (h_inv_le θ) hR.le
    have h_mul2 : R * ‖(circleMap c R θ - w)⁻¹‖ * ‖F_eps n (circleMap c R θ)‖ ≤
        R * (R - dist w c)⁻¹ * max M 0 :=
      mul_le_mul h_mul1 h_fn_le (norm_nonneg _) (mul_nonneg hR.le (inv_nonneg.mpr hd_pos.le))
    rw [← mul_assoc]
    exact h_mul2
  · exact h_bound_int
  · refine ae_of_all _ ?_
    intro θ _hθ
    refine Tendsto.smul tendsto_const_nhds ?_
    refine Tendsto.smul tendsto_const_nhds ?_
    exact h_pt (circleMap c R θ) (h_cm_sphere θ)

lemma limUnder_circleIntegral_cauchy_of_dominated
    {c : ℂ} {R : ℝ} (hR : 0 < R)
    {ι : Type*} {l : Filter ι} [l.NeBot] [l.IsCountablyGenerated]
    (F_eps : ι → ℂ → ℂ) (F_lim : ℂ → ℂ)
    (h_cont : ∀ᶠ n in l, ContinuousOn (F_eps n) (Metric.sphere c R))
    (M : ℝ) (hM : ∀ᶠ n in l, ∀ z ∈ Metric.sphere c R, ‖F_eps n z‖ ≤ M)
    (h_pt : ∀ z ∈ Metric.sphere c R, Filter.Tendsto (fun n => F_eps n z) l (nhds (F_lim z)))
    {w : ℂ} (hw : w ∈ Metric.ball c R) :
    limUnder l (fun n => (2 * Real.pi * Complex.I : ℂ)⁻¹ • ∮ ζ in C(c, R), (ζ - w)⁻¹ • F_eps n ζ) =
      (2 * Real.pi * Complex.I : ℂ)⁻¹ • ∮ ζ in C(c, R), (ζ - w)⁻¹ • F_lim ζ := by
  have h := tendsto_circleIntegral_cauchy_of_dominated hR F_eps F_lim h_cont M hM h_pt hw
  exact h.limUnder_eq

lemma posOrthant_ball_inter_nonempty (n : ℕ) (ρ : ℝ) (hρ_pos : 0 < ρ) :
    (Metric.ball (0 : Fin n → ℂ) ρ ∩ TubeDomain (PosOrthant n)).Nonempty := by
  let z : Fin n → ℂ := fun _ => ((ρ / 2 : ℝ) : ℂ) * Complex.I
  refine ⟨z, ?_, ?_⟩
  · rw [Metric.mem_ball]
    apply (dist_pi_lt_iff hρ_pos).mpr
    intro i
    dsimp [z]
    rw [dist_zero_right, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg (half_pos hρ_pos).le]
    exact half_lt_self hρ_pos
  · intro i
    dsimp [z]
    simp [Complex.mul_im, half_pos hρ_pos]

lemma negOrthant_ball_inter_nonempty (n : ℕ) (ρ : ℝ) (hρ_pos : 0 < ρ) :
    (Metric.ball (0 : Fin n → ℂ) ρ ∩ TubeDomain (NegOrthant n)).Nonempty := by
  let z : Fin n → ℂ := fun _ => - (((ρ / 2 : ℝ) : ℂ) * Complex.I)
  refine ⟨z, ?_, ?_⟩
  · rw [Metric.mem_ball]
    apply (dist_pi_lt_iff hρ_pos).mpr
    intro i
    dsimp [z]
    rw [dist_zero_right, norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg (half_pos hρ_pos).le]
    exact half_lt_self hρ_pos
  · intro i
    dsimp [z]
    simp [Complex.mul_im, half_pos hρ_pos]

lemma analyticAt_circleIntegral_cauchy {K : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hK : CircleIntegrable K c R) {w : ℂ} (hw : w ∈ Metric.ball c R) :
    AnalyticAt ℂ (fun u => (2 * ↑Real.pi * Complex.I : ℂ)⁻¹ •
      ∮ ζ in C(c, R), (ζ - u)⁻¹ • K ζ) w := by
  lift R to NNReal using hR.le
  have hw' : w ∈ Metric.eball c R := by
    rw [Metric.eball_coe]
    exact hw
  have h_series := hasFPowerSeriesOn_cauchy_integral hK hR
  exact h_series.analyticAt_of_mem hw'

lemma orthant_sum_mem_cone_2d
    (V_plus : Set (Fin 2 → ℝ)) (hV_plus_convex : Convex ℝ V_plus)
    (hV_plus_cone : ∀ v ∈ V_plus, ∀ (c : ℝ), c > 0 → (fun i => c * v i) ∈ V_plus)
    (v : Fin 2 → (Fin 2 → ℝ)) (hv : ∀ j, v j ∈ V_plus) :
    (∑ j, v j) ∈ V_plus := by
  have hk_pos : 0 < (2 : ℕ) := by decide
  have h_ones : ∀ j : Fin 2, 0 < (1 : ℝ) := fun _ => by positivity
  have h_sum := sum_pos_smul_mem_of_convex_cone hk_pos hV_plus_convex hV_plus_cone
    v hv (fun _ => 1) h_ones
  have heq_sum : (∑ j, (1 : ℝ) • v j) = ∑ j, v j := by simp
  rwa [heq_sum] at h_sum

lemma orthant_slice_analytic_2d
    (V_plus U : Set (Fin 2 → ℝ))
    (hV_plus_open : IsOpen V_plus)
    (hV_plus_convex : Convex ℝ V_plus)
    (hV_plus_cone : ∀ v ∈ V_plus, ∀ (c : ℝ), c > 0 → (fun i => c * v i) ∈ V_plus)
    (hU_open : IsOpen U)
    (f : (Fin 2 → ℂ) → ℂ)
    (h_cont : ContinuousOn f (WedgeDomain V_plus ((fun v : Fin 2 → ℝ => -v) '' V_plus) U))
    (h_holo_plus : DifferentiableOn ℂ f (TubeDomain V_plus))
    (h_holo_minus : DifferentiableOn ℂ f (TubeDomain ((fun v : Fin 2 → ℝ => -v) '' V_plus)))
    (x : Fin 2 → ℝ) (hx_U : x ∈ U)
    (v : Fin 2 → (Fin 2 → ℝ)) (hv : ∀ j, v j ∈ V_plus) :
    ∃ ρ > 0, AnalyticOnNhd ℂ (slice_fun f (fun i => (x i : ℂ)) (∑ j, v j)) (Metric.ball 0 ρ) := by
  have hu_mem := orthant_sum_mem_cone_2d V_plus hV_plus_convex hV_plus_cone v hv
  have h_slice := slice_analytic_at_zero V_plus U hV_plus_open hV_plus_cone hU_open f h_cont
    h_holo_plus h_holo_minus x hx_U (∑ j, v j) hu_mem
  exact Metric.mem_nhds_iff.mp h_slice.eventually_analyticAt

lemma orthant_slice0_analytic_2d
    (V_plus U : Set (Fin 2 → ℝ))
    (hV_plus_open : IsOpen V_plus)
    (hV_plus_cone : ∀ v ∈ V_plus, ∀ (c : ℝ), c > 0 → (fun i => c * v i) ∈ V_plus)
    (hU_open : IsOpen U)
    (f : (Fin 2 → ℂ) → ℂ)
    (h_cont : ContinuousOn f (WedgeDomain V_plus ((fun v : Fin 2 → ℝ => -v) '' V_plus) U))
    (h_holo_plus : DifferentiableOn ℂ f (TubeDomain V_plus))
    (h_holo_minus : DifferentiableOn ℂ f (TubeDomain ((fun v : Fin 2 → ℝ => -v) '' V_plus)))
    (x : Fin 2 → ℝ) (hx_U : x ∈ U)
    (v : Fin 2 → (Fin 2 → ℝ)) (hv : ∀ j, v j ∈ V_plus) :
    AnalyticAt ℂ (slice_fun f (fun i => (x i : ℂ)) (v 0)) 0 :=
  slice_analytic_at_zero V_plus U hV_plus_open hV_plus_cone hU_open f h_cont
    h_holo_plus h_holo_minus x hx_U (v 0) (hv 0)

lemma orthant_slice1_analytic_2d
    (V_plus U : Set (Fin 2 → ℝ))
    (hV_plus_open : IsOpen V_plus)
    (hV_plus_cone : ∀ v ∈ V_plus, ∀ (c : ℝ), c > 0 → (fun i => c * v i) ∈ V_plus)
    (hU_open : IsOpen U)
    (f : (Fin 2 → ℂ) → ℂ)
    (h_cont : ContinuousOn f (WedgeDomain V_plus ((fun v : Fin 2 → ℝ => -v) '' V_plus) U))
    (h_holo_plus : DifferentiableOn ℂ f (TubeDomain V_plus))
    (h_holo_minus : DifferentiableOn ℂ f (TubeDomain ((fun v : Fin 2 → ℝ => -v) '' V_plus)))
    (x : Fin 2 → ℝ) (hx_U : x ∈ U)
    (v : Fin 2 → (Fin 2 → ℝ)) (hv : ∀ j, v j ∈ V_plus) :
    AnalyticAt ℂ (slice_fun f (fun i => (x i : ℂ)) (v 1)) 0 :=
  slice_analytic_at_zero V_plus U hV_plus_open hV_plus_cone hU_open f h_cont
    h_holo_plus h_holo_minus x hx_U (v 1) (hv 1)

lemma orthant_kernel_holo_plus_2d
    (V_plus : Set (Fin 2 → ℝ)) (hV_plus_convex : Convex ℝ V_plus)
    (hV_plus_cone : ∀ v ∈ V_plus, ∀ (c : ℝ), c > 0 → (fun i => c * v i) ∈ V_plus)
    (f : (Fin 2 → ℂ) → ℂ) (h_holo_plus : DifferentiableOn ℂ f (TubeDomain V_plus))
    (x : Fin 2 → ℝ) (v : Fin 2 → (Fin 2 → ℝ)) (hv : ∀ j, v j ∈ V_plus) :
    DifferentiableOn ℂ (f ∘ cAffine (Matrix.of fun i j => v j i) x)
      (TubeDomain (PosOrthant 2)) := by
  let M : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of fun i j => v j i
  have hn : 0 < (2 : ℕ) := by decide
  exact h_holo_plus.comp (differentiable_cAffine M x).differentiableOn
    (fun w hw => cAffine_mem_tube_plus hn hV_plus_convex hV_plus_cone v hv x w hw)

lemma orthant_kernel_holo_minus_2d
    (V_plus : Set (Fin 2 → ℝ)) (hV_plus_convex : Convex ℝ V_plus)
    (hV_plus_cone : ∀ v ∈ V_plus, ∀ (c : ℝ), c > 0 → (fun i => c * v i) ∈ V_plus)
    (f : (Fin 2 → ℂ) → ℂ)
    (h_holo_minus : DifferentiableOn ℂ f (TubeDomain ((fun v : Fin 2 → ℝ => -v) '' V_plus)))
    (x : Fin 2 → ℝ) (v : Fin 2 → (Fin 2 → ℝ)) (hv : ∀ j, v j ∈ V_plus) :
    DifferentiableOn ℂ (f ∘ cAffine (Matrix.of fun i j => v j i) x)
      (TubeDomain (NegOrthant 2)) := by
  let M : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of fun i j => v j i
  have hn : 0 < (2 : ℕ) := by decide
  exact h_holo_minus.comp (differentiable_cAffine M x).differentiableOn
    (fun w hw => cAffine_mem_tube_minus hn hV_plus_convex hV_plus_cone v hv x w hw)

lemma orthant_kernel_slice0_analytic_2d
    (V_plus U : Set (Fin 2 → ℝ))
    (hV_plus_open : IsOpen V_plus)
    (hV_plus_cone : ∀ v ∈ V_plus, ∀ (c : ℝ), c > 0 → (fun i => c * v i) ∈ V_plus)
    (hU_open : IsOpen U)
    (f : (Fin 2 → ℂ) → ℂ)
    (h_cont : ContinuousOn f (WedgeDomain V_plus ((fun v : Fin 2 → ℝ => -v) '' V_plus) U))
    (h_holo_plus : DifferentiableOn ℂ f (TubeDomain V_plus))
    (h_holo_minus : DifferentiableOn ℂ f (TubeDomain ((fun v : Fin 2 → ℝ => -v) '' V_plus)))
    (x : Fin 2 → ℝ) (hx_U : x ∈ U)
    (v : Fin 2 → (Fin 2 → ℝ)) (hv : ∀ j, v j ∈ V_plus) :
    AnalyticAt ℂ
      (fun t : ℂ => (f ∘ cAffine (Matrix.of fun i j => v j i) x)
        (fun i => if i = 0 then t else 0)) 0 := by
  have heq :
      (fun t : ℂ => (f ∘ cAffine (Matrix.of fun i j => v j i) x)
        (fun i => if i = 0 then t else 0)) =
      slice_fun f (fun i => (x i : ℂ)) (v 0) := by
    ext t
    dsimp [Function.comp, slice_fun]
    congr 1
    ext i
    fin_cases i
    · dsimp [cAffine, Matrix.mulVec, dotProduct]; simp; ring
    · dsimp [cAffine, Matrix.mulVec, dotProduct]; simp; ring
  rw [heq]
  exact orthant_slice0_analytic_2d V_plus U hV_plus_open hV_plus_cone hU_open f h_cont
    h_holo_plus h_holo_minus x hx_U v hv

lemma orthant_kernel_slice1_analytic_2d
    (V_plus U : Set (Fin 2 → ℝ))
    (hV_plus_open : IsOpen V_plus)
    (hV_plus_cone : ∀ v ∈ V_plus, ∀ (c : ℝ), c > 0 → (fun i => c * v i) ∈ V_plus)
    (hU_open : IsOpen U)
    (f : (Fin 2 → ℂ) → ℂ)
    (h_cont : ContinuousOn f (WedgeDomain V_plus ((fun v : Fin 2 → ℝ => -v) '' V_plus) U))
    (h_holo_plus : DifferentiableOn ℂ f (TubeDomain V_plus))
    (h_holo_minus : DifferentiableOn ℂ f (TubeDomain ((fun v : Fin 2 → ℝ => -v) '' V_plus)))
    (x : Fin 2 → ℝ) (hx_U : x ∈ U)
    (v : Fin 2 → (Fin 2 → ℝ)) (hv : ∀ j, v j ∈ V_plus) :
    AnalyticAt ℂ
      (fun t : ℂ => (f ∘ cAffine (Matrix.of fun i j => v j i) x)
        (fun i => if i = 1 then t else 0)) 0 := by
  have heq :
      (fun t : ℂ => (f ∘ cAffine (Matrix.of fun i j => v j i) x)
        (fun i => if i = 1 then t else 0)) =
      slice_fun f (fun i => (x i : ℂ)) (v 1) := by
    ext t
    dsimp [Function.comp, slice_fun]
    congr 1
    ext i
    fin_cases i
    · dsimp [cAffine, Matrix.mulVec, dotProduct]; simp; ring
    · dsimp [cAffine, Matrix.mulVec, dotProduct]; simp; ring
  rw [heq]
  exact orthant_slice1_analytic_2d V_plus U hV_plus_open hV_plus_cone hU_open f h_cont
    h_holo_plus h_holo_minus x hx_U v hv

lemma orthant_kernel_diag_analytic_2d
    (f : (Fin 2 → ℂ) → ℂ) (x : Fin 2 → ℝ) (v : Fin 2 → (Fin 2 → ℝ))
    (ρ : ℝ)
    (hg_an : AnalyticOnNhd ℂ (slice_fun f (fun i => (x i : ℂ)) (∑ j, v j)) (Metric.ball 0 ρ)) :
    AnalyticOnNhd ℂ (fun t : ℂ => (f ∘ cAffine (Matrix.of fun i j => v j i) x) (fun _ => t))
      (Metric.ball 0 ρ) := by
  have heq : (fun t : ℂ => (f ∘ cAffine (Matrix.of fun i j => v j i) x) (fun _ => t)) =
      slice_fun f (fun i => (x i : ℂ)) (∑ j, v j) := by
    ext t
    dsimp [Function.comp, slice_fun]
    congr 1
    ext i
    fin_cases i
    · dsimp [cAffine, Matrix.mulVec, dotProduct]; simp [Fin.sum_univ_two]; ring
    · dsimp [cAffine, Matrix.mulVec, dotProduct]; simp [Fin.sum_univ_two]; ring
  rw [heq]
  exact hg_an

lemma orthant_kernel_diag_analytic_nd (n : ℕ) (hn : 0 < n)
    (f : (Fin n → ℂ) → ℂ) (x : Fin n → ℝ) (v : Fin n → (Fin n → ℝ))
    (ρ : ℝ)
    (hg_an : AnalyticOnNhd ℂ (slice_fun f (fun i => (x i : ℂ)) (∑ j, v j)) (Metric.ball 0 ρ))
    (w : Fin n → ℂ) (hw : w ∈ Metric.ball 0 ρ) (hdiag : ∀ i, w i = w ⟨0, hn⟩) :
    ∃ F : (Fin n → ℂ) → ℂ, AnalyticAt ℂ F w ∧
      F w = (f ∘ cAffine (Matrix.of fun i j => v j i) x) w := by
  have hw0 : w ⟨0, hn⟩ ∈ Metric.ball (0 : ℂ) ρ := by
    rw [Metric.mem_ball] at hw ⊢
    have hle := dist_le_pi_dist w 0 ⟨0, hn⟩
    exact lt_of_le_of_lt hle hw
  let P : (Fin n → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj ⟨0, hn⟩
  have hP : AnalyticAt ℂ P w := P.analyticAt w
  let G1 : ℂ → ℂ := slice_fun f (fun i => (x i : ℂ)) (∑ j, v j)
  have hG1 : AnalyticAt ℂ G1 (P w) := hg_an (w ⟨0, hn⟩) hw0
  have h_comp : AnalyticAt ℂ (G1 ∘ P) w := hG1.comp hP
  use (G1 ∘ P)
  refine ⟨h_comp, ?_⟩
  dsimp [G1, Function.comp, slice_fun, P]
  congr 1
  ext i
  dsimp [cAffine, Matrix.mulVec, dotProduct]
  have heq : (∑ j : Fin n, (v j i : ℂ) * w j) = (∑ j : Fin n, (v j i : ℂ) * w ⟨0, hn⟩) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [hdiag j]
  rw [heq, ← Finset.sum_mul]
  have hsum : ((∑ j : Fin n, v j) i : ℂ) = ∑ j : Fin n, (v j i : ℂ) := by
    simp [Finset.sum_apply]
  rw [hsum]
  ring

lemma orthant_kernel_analytic_1d
    (f : (Fin 1 → ℂ) → ℂ) (x : Fin 1 → ℝ) (v : Fin 1 → (Fin 1 → ℝ))
    (ρ : ℝ)
    (hg_an : AnalyticOnNhd ℂ (slice_fun f (fun i => (x i : ℂ)) (∑ j, v j)) (Metric.ball 0 ρ)) :
    AnalyticOnNhd ℂ (f ∘ cAffine (Matrix.of fun i j => v j i) x) (Metric.ball 0 ρ) := by
  intro w hw
  have hw0 : w 0 ∈ Metric.ball (0 : ℂ) ρ := by
    rw [Metric.mem_ball] at hw ⊢
    have hle := dist_le_pi_dist w 0 0
    exact lt_of_le_of_lt hle hw
  let P : (Fin 1 → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj 0
  have hP : AnalyticAt ℂ P w := P.analyticAt w
  let G1 : ℂ → ℂ := slice_fun f (fun i => (x i : ℂ)) (∑ j, v j)
  have hG1 : AnalyticAt ℂ G1 (P w) := hg_an (w 0) hw0
  have h_comp : AnalyticAt ℂ (G1 ∘ P) w := hG1.comp hP
  have heq : (f ∘ cAffine (Matrix.of fun i j => v j i) x) = G1 ∘ P := by
    ext u
    dsimp [G1, Function.comp, slice_fun, P]
    congr 1
    ext i
    fin_cases i
    dsimp [cAffine, Matrix.mulVec, dotProduct]
    simp
    ring
  rw [heq]
  exact h_comp

lemma orthant_kernel_diag_pullback_2d
    (f : (Fin 2 → ℂ) → ℂ) (x : Fin 2 → ℝ) (v : Fin 2 → (Fin 2 → ℝ))
    (ρ : ℝ)
    (hg_an : AnalyticOnNhd ℂ (slice_fun f (fun i => (x i : ℂ)) (∑ j, v j)) (Metric.ball 0 ρ))
    (w : Fin 2 → ℂ) (hw : w ∈ Metric.ball 0 ρ) :
    AnalyticAt ℂ
      (fun u : Fin 2 → ℂ => (f ∘ cAffine (Matrix.of fun i j => v j i) x) (fun _ => u 0)) w := by
  have hw0 : w 0 ∈ Metric.ball (0 : ℂ) ρ := by
    rw [Metric.mem_ball] at hw ⊢
    have hle := dist_le_pi_dist w 0 0
    exact lt_of_le_of_lt hle hw
  let P : (Fin 2 → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj 0
  have hP : AnalyticAt ℂ P w := P.analyticAt w
  let G1 : ℂ → ℂ := slice_fun f (fun i => (x i : ℂ)) (∑ j, v j)
  have hG1 : AnalyticAt ℂ G1 (P w) := hg_an (w 0) hw0
  have h_comp : AnalyticAt ℂ (G1 ∘ P) w := hG1.comp hP
  have heq :
      (fun u : Fin 2 → ℂ => (f ∘ cAffine (Matrix.of fun i j => v j i) x) (fun _ => u 0)) =
      G1 ∘ P := by
    ext u
    dsimp [G1, Function.comp, slice_fun, P]
    congr 1
    ext i; fin_cases i
    · dsimp [cAffine, Matrix.mulVec, dotProduct]; simp [Fin.sum_univ_two]; ring
    · dsimp [cAffine, Matrix.mulVec, dotProduct]; simp [Fin.sum_univ_two]; ring
  rw [heq]
  exact h_comp

lemma cAffine_consFin_eq {k : ℕ} (v : Fin (k + 1) → (Fin (k + 1) → ℝ)) (x : Fin (k + 1) → ℝ)
    (w' : Fin k → ℂ) (z : ℂ) (i : Fin (k + 1)) :
    cAffine (Matrix.of fun i j => v j i) x (consFin w' z) i =
      (x i : ℂ) + (∑ j : Fin k, (v (Fin.castSucc j) i : ℂ) * w' j) +
        (v (Fin.last k) i : ℂ) * z := by
  dsimp [cAffine, Matrix.mulVec, dotProduct]
  rw [Fin.sum_univ_castSucc]
  simp [consFin]
  ring

lemma orthant_kernel_polydisc_radius_nd (n : ℕ) (w : Fin n → ℂ) (ρ : ℝ) (hw : w ∈ Metric.ball 0 ρ) :
    let r : Fin n → ℝ := fun i => (ρ - dist (w i) 0) / 2
    (∀ i, 0 < r i) ∧ (∀ i, dist (w i) 0 + r i < ρ) ∧
    (∀ i, Metric.closedBall (w i) (r i) ⊆ Metric.ball (0 : ℂ) ρ) := by
  intro r
  have hr_pos : ∀ i, 0 < r i := by
    intro i
    have hwi : dist (w i) 0 < ρ := lt_of_le_of_lt (dist_le_pi_dist w 0 i) (Metric.mem_ball.mp hw)
    dsimp [r]; linarith
  have hr_sum : ∀ i, dist (w i) 0 + r i < ρ := by
    intro i
    have hwi : dist (w i) 0 < ρ := lt_of_le_of_lt (dist_le_pi_dist w 0 i) (Metric.mem_ball.mp hw)
    dsimp [r]; linarith
  have h_sub : ∀ i, Metric.closedBall (w i) (r i) ⊆ Metric.ball (0 : ℂ) ρ := by
    intro i z hz
    rw [Metric.mem_closedBall] at hz
    rw [Metric.mem_ball]
    have h_tri := dist_triangle z (w i) 0
    have hwi : dist (w i) 0 < ρ := lt_of_le_of_lt (dist_le_pi_dist w 0 i) (Metric.mem_ball.mp hw)
    dsimp [r] at hz ⊢
    linarith
  exact ⟨hr_pos, hr_sum, h_sub⟩

lemma orthant_kernel_torus_analytic_2d
    (w : Fin 2 → ℂ) (ρ : ℝ) (hw : w ∈ Metric.ball 0 ρ) :
    let c : Fin 2 → ℂ := w
    let r : Fin 2 → ℝ := fun i => (ρ - dist (w i) 0) / 2
    ∀ ζ₀ ∈ Metric.sphere (c 0) (r 0), ∀ ζ₁ ∈ Metric.sphere (c 1) (r 1),
      AnalyticAt ℂ (fun u : Fin 2 → ℂ => (ζ₀ - u 0)⁻¹ * (ζ₁ - u 1)⁻¹) w := by
  intro c r ζ₀ h0 ζ₁ h1
  rcases orthant_kernel_polydisc_radius_nd 2 w ρ hw with ⟨hr_pos, _, _⟩
  have h_ne0 : ζ₀ ≠ w 0 := by
    rw [Metric.mem_sphere] at h0
    intro h_eq
    dsimp [c] at h0; subst h_eq; rw [dist_self] at h0
    have hr0 := hr_pos 0; dsimp [r] at h0; linarith
  have h_ne1 : ζ₁ ≠ w 1 := by
    rw [Metric.mem_sphere] at h1
    intro h_eq
    dsimp [c] at h1; subst h_eq; rw [dist_self] at h1
    have hr1 := hr_pos 1; dsimp [r] at h1; linarith
  exact analyticAt_cauchy_kernel_prod h_ne0 h_ne1

lemma analyticAt_of_eventuallyEq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {g F : E → ℂ} {w : E} (hF : AnalyticAt ℂ F w) (h_eq : F =ᶠ[nhds w] g) :
    AnalyticAt ℂ g w := hF.congr h_eq

lemma orthant_kernel_diag_proj_analytic (n : ℕ) (hn : 0 < n)
    (f : (Fin n → ℂ) → ℂ) (x : Fin n → ℝ) (v : Fin n → (Fin n → ℝ))
    (ρ : ℝ)
    (hg_an : AnalyticOnNhd ℂ (slice_fun f (fun i => (x i : ℂ)) (∑ j, v j)) (Metric.ball 0 ρ))
    (w : Fin n → ℂ) (hw : w ∈ Metric.ball 0 ρ) :
    AnalyticAt ℂ ((slice_fun f (fun i => (x i : ℂ)) (∑ j, v j)) ∘
      ((ContinuousLinearMap.proj ⟨0, hn⟩ : (Fin n → ℂ) →L[ℂ] ℂ))) w := by
  have hw0 : w ⟨0, hn⟩ ∈ Metric.ball (0 : ℂ) ρ := by
    rw [Metric.mem_ball] at hw ⊢
    have hle := dist_le_pi_dist w 0 ⟨0, hn⟩
    exact lt_of_le_of_lt hle hw
  let P : (Fin n → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj ⟨0, hn⟩
  have hP : AnalyticAt ℂ P w := P.analyticAt w
  let G1 : ℂ → ℂ := slice_fun f (fun i => (x i : ℂ)) (∑ j, v j)
  have hG1 : AnalyticAt ℂ G1 (P w) := hg_an (w ⟨0, hn⟩) hw0
  exact hG1.comp hP

lemma cAffine_diag_eq (n : ℕ) (_hn : 0 < n)
    (f : (Fin n → ℂ) → ℂ) (x : Fin n → ℝ) (v : Fin n → (Fin n → ℝ)) (t : ℂ) :
    (f ∘ cAffine (Matrix.of fun i j => v j i) x) (fun _ => t) =
      slice_fun f (fun i => (x i : ℂ)) (∑ j, v j) t := by
  dsimp [slice_fun, Function.comp]
  congr 1
  ext i
  dsimp [cAffine, Matrix.mulVec, dotProduct]
  congr 1
  rw [← Finset.sum_mul]
  have hsum : ((∑ j : Fin n, v j) i : ℂ) = ∑ j : Fin n, (v j i : ℂ) := by
    simp [Finset.sum_apply]
  rw [hsum, mul_comm]

lemma orthant_kernel_analytic_2d_cauchy_rep
    (w : Fin 2 → ℂ) (ρ : ℝ) (hw : w ∈ Metric.ball 0 ρ) :
    let c : Fin 2 → ℂ := w
    let r : Fin 2 → ℝ := fun i => (ρ - dist (w i) 0) / 2
    (∀ i : Fin 2, 0 < r i) ∧
    (∀ i : Fin 2, w i ∈ Metric.ball (c i) (r i)) ∧
    (∀ ζ₀ ∈ Metric.sphere (c 0) (r 0), ∀ ζ₁ ∈ Metric.sphere (c 1) (r 1),
      AnalyticAt ℂ (fun u : Fin 2 → ℂ => (ζ₀ - u 0)⁻¹ * (ζ₁ - u 1)⁻¹) w) := by
  intro c r
  rcases orthant_kernel_polydisc_radius_nd 2 w ρ hw with ⟨hr_pos, _, _⟩
  have hw_in : ∀ i : Fin 2, w i ∈ Metric.ball (c i) (r i) := by
    intro i; dsimp [c]; rw [Metric.mem_ball, dist_self]; exact hr_pos i
  have h_torus := orthant_kernel_torus_analytic_2d w ρ hw
  exact ⟨hr_pos, hw_in, h_torus⟩

lemma orthant_kernel_analytic_nd_cauchy_rep (n : ℕ) (_hn : 0 < n)
    (w : Fin n → ℂ) (ρ : ℝ) (hw : w ∈ Metric.ball 0 ρ) :
    let c : Fin n → ℂ := w
    let r : Fin n → ℝ := fun i => (ρ - dist (w i) 0) / 2
    (∀ i : Fin n, 0 < r i) ∧
    (∀ i : Fin n, w i ∈ Metric.ball (c i) (r i)) ∧
    (∀ i : Fin n, ∀ ζ ∈ Metric.sphere (c i) (r i), ζ ≠ w i) := by
  intro c r
  rcases orthant_kernel_polydisc_radius_nd n w ρ hw with ⟨hr_pos, _, _⟩
  have hw_in : ∀ i : Fin n, w i ∈ Metric.ball (c i) (r i) := by
    intro i; dsimp [c]; rw [Metric.mem_ball, dist_self]; exact hr_pos i
  have h_ne : ∀ i : Fin n, ∀ ζ ∈ Metric.sphere (c i) (r i), ζ ≠ w i := by
    intro i ζ hζ h_eq
    rw [Metric.mem_sphere] at hζ
    dsimp [c] at hζ; subst h_eq; rw [dist_self] at hζ
    have hri := hr_pos i; dsimp [r] at hζ; linarith
  exact ⟨hr_pos, hw_in, h_ne⟩

lemma orthant_kernel_analytic_2d_local
    (f : (Fin 2 → ℂ) → ℂ) (x : Fin 2 → ℝ) (v : Fin 2 → (Fin 2 → ℝ))
    (ρ : ℝ)
    (hg_an : AnalyticOnNhd ℂ (slice_fun f (fun i => (x i : ℂ)) (∑ j, v j)) (Metric.ball 0 ρ))
    (w : Fin 2 → ℂ) (hw : w ∈ Metric.ball 0 ρ) :
    ∃ F : (Fin 2 → ℂ) → ℂ, AnalyticAt ℂ F w ∧
      F = (slice_fun f (fun i => (x i : ℂ)) (∑ j, v j)) ∘
        ((ContinuousLinearMap.proj ⟨0, by decide⟩ : (Fin 2 → ℂ) →L[ℂ] ℂ)) :=
  ⟨_, orthant_kernel_diag_proj_analytic 2 (by decide) f x v ρ hg_an w hw, rfl⟩

lemma orthant_kernel_analytic_nd_local (n : ℕ) (hn : 0 < n)
    (f : (Fin n → ℂ) → ℂ) (x : Fin n → ℝ) (v : Fin n → (Fin n → ℝ))
    (ρ : ℝ)
    (hg_an : AnalyticOnNhd ℂ (slice_fun f (fun i => (x i : ℂ)) (∑ j, v j)) (Metric.ball 0 ρ))
    (w : Fin n → ℂ) (hw : w ∈ Metric.ball 0 ρ) :
    ∃ F : (Fin n → ℂ) → ℂ, AnalyticAt ℂ F w ∧
      F = (slice_fun f (fun i => (x i : ℂ)) (∑ j, v j)) ∘
        ((ContinuousLinearMap.proj ⟨0, hn⟩ : (Fin n → ℂ) →L[ℂ] ℂ)) :=
  ⟨_, orthant_kernel_diag_proj_analytic n hn f x v ρ hg_an w hw, rfl⟩

lemma orthant_kernel_analytic_2d_pt_of_local
    (f : (Fin 2 → ℂ) → ℂ) (x : Fin 2 → ℝ) (v : Fin 2 → (Fin 2 → ℝ))
    (ρ : ℝ)
    (hg_an : AnalyticOnNhd ℂ (slice_fun f (fun i => (x i : ℂ)) (∑ j, v j)) (Metric.ball 0 ρ))
    (w : Fin 2 → ℂ) (hw : w ∈ Metric.ball 0 ρ)
    (h_eq : (f ∘ cAffine (Matrix.of fun i j => v j i) x) =ᶠ[nhds w]
      ((slice_fun f (fun i => (x i : ℂ)) (∑ j, v j)) ∘
        ((ContinuousLinearMap.proj ⟨0, by decide⟩ : (Fin 2 → ℂ) →L[ℂ] ℂ)))) :
    AnalyticAt ℂ (f ∘ cAffine (Matrix.of fun i j => v j i) x) w := by
  have h_proj := orthant_kernel_diag_proj_analytic 2 (by decide) f x v ρ hg_an w hw
  exact analyticAt_of_eventuallyEq h_proj h_eq.symm

lemma orthant_kernel_analytic_nd_pt_of_local (n : ℕ) (hn : 0 < n)
    (f : (Fin n → ℂ) → ℂ) (x : Fin n → ℝ) (v : Fin n → (Fin n → ℝ))
    (ρ : ℝ)
    (hg_an : AnalyticOnNhd ℂ (slice_fun f (fun i => (x i : ℂ)) (∑ j, v j)) (Metric.ball 0 ρ))
    (w : Fin n → ℂ) (hw : w ∈ Metric.ball 0 ρ)
    (h_eq : (f ∘ cAffine (Matrix.of fun i j => v j i) x) =ᶠ[nhds w]
      ((slice_fun f (fun i => (x i : ℂ)) (∑ j, v j)) ∘
        ((ContinuousLinearMap.proj ⟨0, hn⟩ : (Fin n → ℂ) →L[ℂ] ℂ)))) :
    AnalyticAt ℂ (f ∘ cAffine (Matrix.of fun i j => v j i) x) w := by
  have h_proj := orthant_kernel_diag_proj_analytic n hn f x v ρ hg_an w hw
  exact analyticAt_of_eventuallyEq h_proj h_eq.symm

lemma orthant_kernel_analytic_2d_pt_closure
    (f : (Fin 2 → ℂ) → ℂ) (x : Fin 2 → ℝ) (v : Fin 2 → (Fin 2 → ℝ))
    (_ρ : ℝ)
    (_hg_an : AnalyticOnNhd ℂ (slice_fun f (fun i => (x i : ℂ)) (∑ j, v j)) (Metric.ball 0 _ρ))
    (w : Fin 2 → ℂ) (_hw : w ∈ Metric.ball 0 _ρ)
    (F : (Fin 2 → ℂ) → ℂ) (hF_an : AnalyticAt ℂ F w)
    (h_eq : (f ∘ cAffine (Matrix.of fun i j => v j i) x) =ᶠ[nhds w] F) :
    AnalyticAt ℂ (f ∘ cAffine (Matrix.of fun i j => v j i) x) w :=
  analyticAt_of_eventuallyEq hF_an h_eq.symm

lemma orthant_kernel_analytic_nd_step_closure (n : ℕ) (_hn : 0 < n)
    (f : (Fin n → ℂ) → ℂ) (x : Fin n → ℝ) (v : Fin n → (Fin n → ℝ))
    (_ρ : ℝ)
    (_hg_an : AnalyticOnNhd ℂ (slice_fun f (fun i => (x i : ℂ)) (∑ j, v j)) (Metric.ball 0 _ρ))
    (w : Fin n → ℂ) (_hw : w ∈ Metric.ball 0 _ρ)
    (F : (Fin n → ℂ) → ℂ) (hF_an : AnalyticAt ℂ F w)
    (h_eq : (f ∘ cAffine (Matrix.of fun i j => v j i) x) =ᶠ[nhds w] F) :
    AnalyticAt ℂ (f ∘ cAffine (Matrix.of fun i j => v j i) x) w :=
  analyticAt_of_eventuallyEq hF_an h_eq.symm

lemma orthant_kernel_2d_diag_ident
    (f : (Fin 2 → ℂ) → ℂ) (x : Fin 2 → ℝ) (v : Fin 2 → (Fin 2 → ℝ)) (t : ℂ) :
    (f ∘ cAffine (Matrix.of fun i j => v j i) x) (fun _ => t) =
      slice_fun f (fun i => (x i : ℂ)) (∑ j, v j) t := by
  dsimp [slice_fun, Function.comp]
  congr 1
  ext i
  dsimp [cAffine, Matrix.mulVec, dotProduct]
  congr 1
  rw [← Finset.sum_mul]
  have hsum : ((∑ j : Fin 2, v j) i : ℂ) = ∑ j : Fin 2, (v j i : ℂ) := by
    simp [Finset.sum_apply]
  rw [hsum, mul_comm]

lemma orthant_kernel_2d_diag_proj_comp
    (f : (Fin 2 → ℂ) → ℂ) (x : Fin 2 → ℝ) (v : Fin 2 → (Fin 2 → ℝ)) :
    (fun u : Fin 2 → ℂ => (f ∘ cAffine (Matrix.of fun i j => v j i) x) (fun _ => u 0)) =
      ((slice_fun f (fun i => (x i : ℂ)) (∑ j, v j)) ∘
        ((ContinuousLinearMap.proj ⟨0, by decide⟩ : (Fin 2 → ℂ) →L[ℂ] ℂ))) := by
  ext u
  dsimp [Function.comp]
  exact orthant_kernel_2d_diag_ident f x v (u 0)

lemma orthant_kernel_2d_diag_eval_eq
    (w : Fin 2 → ℂ) (hdiag : w 0 = w 1) :
    (fun _ => w 0) = w := by
  ext i; fin_cases i
  · rfl
  · exact hdiag

lemma orthant_kernel_2d_eval_on_diag
    (f : (Fin 2 → ℂ) → ℂ) (x : Fin 2 → ℝ) (v : Fin 2 → (Fin 2 → ℝ))
    (w : Fin 2 → ℂ) (hdiag : w 0 = w 1) :
    (f ∘ cAffine (Matrix.of fun i j => v j i) x) w =
      ((slice_fun f (fun i => (x i : ℂ)) (∑ j, v j)) ∘
        ((ContinuousLinearMap.proj ⟨0, by decide⟩ : (Fin 2 → ℂ) →L[ℂ] ℂ))) w := by
  have heq := orthant_kernel_2d_diag_eval_eq w hdiag
  rw [← heq]
  have hcomp := congr_fun (orthant_kernel_2d_diag_proj_comp f x v) w
  exact hcomp

lemma orthant_kernel_nd_diag_ident (n : ℕ) (_hn : 0 < n)
    (f : (Fin n → ℂ) → ℂ) (x : Fin n → ℝ) (v : Fin n → (Fin n → ℝ)) (t : ℂ) :
    (f ∘ cAffine (Matrix.of fun i j => v j i) x) (fun _ => t) =
      slice_fun f (fun i => (x i : ℂ)) (∑ j, v j) t := by
  dsimp [slice_fun, Function.comp]
  congr 1
  ext i
  dsimp [cAffine, Matrix.mulVec, dotProduct]
  congr 1
  rw [← Finset.sum_mul]
  have hsum : ((∑ j : Fin n, v j) i : ℂ) = ∑ j : Fin n, (v j i : ℂ) := by
    simp [Finset.sum_apply]
  rw [hsum, mul_comm]

lemma orthant_kernel_nd_diag_proj_comp (n : ℕ) (hn : 0 < n)
    (f : (Fin n → ℂ) → ℂ) (x : Fin n → ℝ) (v : Fin n → (Fin n → ℝ)) :
    (fun u : Fin n → ℂ => (f ∘ cAffine (Matrix.of fun i j => v j i) x) (fun _ => u ⟨0, hn⟩)) =
      ((slice_fun f (fun i => (x i : ℂ)) (∑ j, v j)) ∘
        ((ContinuousLinearMap.proj ⟨0, hn⟩ : (Fin n → ℂ) →L[ℂ] ℂ))) := by
  ext u
  dsimp [Function.comp]
  exact orthant_kernel_nd_diag_ident n hn f x v (u ⟨0, hn⟩)

lemma orthant_kernel_nd_diag_eval_eq (n : ℕ) (hn : 0 < n)
    (w : Fin n → ℂ) (hdiag : ∀ i, w i = w ⟨0, hn⟩) :
    (fun _ => w ⟨0, hn⟩) = w := by
  ext i
  exact (hdiag i).symm

lemma orthant_kernel_nd_eval_on_diag (n : ℕ) (hn : 0 < n)
    (f : (Fin n → ℂ) → ℂ) (x : Fin n → ℝ) (v : Fin n → (Fin n → ℝ))
    (w : Fin n → ℂ) (hdiag : ∀ i, w i = w ⟨0, hn⟩) :
    (f ∘ cAffine (Matrix.of fun i j => v j i) x) w =
      ((slice_fun f (fun i => (x i : ℂ)) (∑ j, v j)) ∘
        ((ContinuousLinearMap.proj ⟨0, hn⟩ : (Fin n → ℂ) →L[ℂ] ℂ))) w := by
  have heq := orthant_kernel_nd_diag_eval_eq n hn w hdiag
  rw [← heq]
  have hcomp := congr_fun (orthant_kernel_nd_diag_proj_comp n hn f x v) w
  exact hcomp

lemma orthant_kernel_2d_eq_slice
    (f : (Fin 2 → ℂ) → ℂ) (x : Fin 2 → ℝ) (v : Fin 2 → (Fin 2 → ℝ))
    (_ρ : ℝ)
    (_hg_an : AnalyticOnNhd ℂ (slice_fun f (fun i => (x i : ℂ)) (∑ j, v j)) (Metric.ball 0 _ρ))
    (w : Fin 2 → ℂ) (_hw : w ∈ Metric.ball 0 _ρ) (hdiag : w 0 = w 1) :
    (f ∘ cAffine (Matrix.of fun i j => v j i) x) w =
      ((slice_fun f (fun i => (x i : ℂ)) (∑ j, v j)) ∘
        ((ContinuousLinearMap.proj ⟨0, by decide⟩ : (Fin 2 → ℂ) →L[ℂ] ℂ))) w :=
  orthant_kernel_2d_eval_on_diag f x v w hdiag

lemma orthant_kernel_nd_eq_slice (n : ℕ) (hn : 0 < n)
    (f : (Fin n → ℂ) → ℂ) (x : Fin n → ℝ) (v : Fin n → (Fin n → ℝ))
    (_ρ : ℝ)
    (_hg_an : AnalyticOnNhd ℂ (slice_fun f (fun i => (x i : ℂ)) (∑ j, v j)) (Metric.ball 0 _ρ))
    (w : Fin n → ℂ) (_hw : w ∈ Metric.ball 0 _ρ) (hdiag : ∀ i, w i = w ⟨0, hn⟩) :
    (f ∘ cAffine (Matrix.of fun i j => v j i) x) w =
      ((slice_fun f (fun i => (x i : ℂ)) (∑ j, v j)) ∘
        ((ContinuousLinearMap.proj ⟨0, hn⟩ : (Fin n → ℂ) →L[ℂ] ℂ))) w :=
  orthant_kernel_nd_eval_on_diag n hn f x v w hdiag

lemma orthant_kernel_cauchy_2d_eq
    (g : (Fin 2 → ℂ) → ℂ) (c : Fin 2 → ℂ) (r : Fin 2 → ℝ)
    (_hr_pos : ∀ i, 0 < r i) (w : Fin 2 → ℂ) (hw : ∀ i, w i ∈ Metric.ball (c i) (r i))
    (h_rep : ∀ u, (∀ i, u i ∈ Metric.ball (c i) (r i)) → iteratedCauchyIntegral2 g c r u = g u) :
    iteratedCauchyIntegral2 g c r =ᶠ[nhds w] g := by
  have heq : {u : Fin 2 → ℂ | ∀ i, u i ∈ Metric.ball (c i) (r i)} =
      Set.pi Set.univ (fun i => Metric.ball (c i) (r i)) := by
    ext u; simp
  have h_open : IsOpen {u : Fin 2 → ℂ | ∀ i, u i ∈ Metric.ball (c i) (r i)} := by
    rw [heq]
    exact isOpen_set_pi Set.finite_univ (fun i _ => Metric.isOpen_ball)
  have h_mem : w ∈ {u : Fin 2 → ℂ | ∀ i, u i ∈ Metric.ball (c i) (r i)} := hw
  have h_nhds := h_open.mem_nhds h_mem
  exact Filter.eventuallyEq_iff_exists_mem.mpr ⟨_, h_nhds, fun u hu => h_rep u hu⟩

lemma orthant_kernel_cauchy_nd_eq (n : ℕ)
    (g : (Fin n → ℂ) → ℂ) (c : Fin n → ℂ) (r : Fin n → ℝ)
    (_hr_pos : ∀ i, 0 < r i) (w : Fin n → ℂ) (hw : ∀ i, w i ∈ Metric.ball (c i) (r i))
    (h_rep : ∀ u, (∀ i, u i ∈ Metric.ball (c i) (r i)) → iteratedCauchy n g c r u = g u) :
    iteratedCauchy n g c r =ᶠ[nhds w] g := by
  have heq : {u : Fin n → ℂ | ∀ i, u i ∈ Metric.ball (c i) (r i)} =
      Set.pi Set.univ (fun i => Metric.ball (c i) (r i)) := by
    ext u; simp
  have h_open : IsOpen {u : Fin n → ℂ | ∀ i, u i ∈ Metric.ball (c i) (r i)} := by
    rw [heq]
    exact isOpen_set_pi Set.finite_univ (fun i _ => Metric.isOpen_ball)
  have h_mem : w ∈ {u : Fin n → ℂ | ∀ i, u i ∈ Metric.ball (c i) (r i)} := hw
  have h_nhds := h_open.mem_nhds h_mem
  exact Filter.eventuallyEq_iff_exists_mem.mpr ⟨_, h_nhds, fun u hu => h_rep u hu⟩

def OrthantEOWData (n : ℕ) (g : (Fin n → ℂ) → ℂ) (ρ : ℝ) : Prop :=
  DifferentiableOn ℂ g (Metric.ball 0 ρ ∩ TubeDomain (PosOrthant n)) ∧
  DifferentiableOn ℂ g (Metric.ball 0 ρ ∩ TubeDomain (NegOrthant n)) ∧
  ContinuousOn g (Metric.ball 0 ρ ∩
    (TubeDomain (PosOrthant n) ∪ TubeDomain (NegOrthant n) ∪
      {w : Fin n → ℂ | ∀ i, (w i).im = 0}))

lemma orthant_eowData_of_wedge (n : ℕ) (hn : 0 < n)
    (V_plus U : Set (Fin n → ℝ))
    (hV_plus_convex : Convex ℝ V_plus)
    (hV_plus_cone : ∀ v ∈ V_plus, ∀ (c : ℝ), c > 0 → (fun i => c * v i) ∈ V_plus)
    (hU_open : IsOpen U)
    (f : (Fin n → ℂ) → ℂ)
    (h_cont : ContinuousOn f (WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U))
    (h_holo_plus : DifferentiableOn ℂ f (TubeDomain V_plus))
    (h_holo_minus : DifferentiableOn ℂ f (TubeDomain ((fun v : Fin n → ℝ => -v) '' V_plus)))
    (x : Fin n → ℝ) (hx_U : x ∈ U)
    (v : Fin n → (Fin n → ℝ)) (hv : ∀ j, v j ∈ V_plus) :
    ∃ ρ : ℝ, 0 < ρ ∧
      OrthantEOWData n (f ∘ cAffine (Matrix.of fun i j => v j i) x) ρ := by
  have hcont_aff : Continuous (cAffine (Matrix.of fun i j => v j i) x) :=
    (differentiable_cAffine _ x).continuous
  have hre_cont : Continuous
      (fun w : Fin n → ℂ => fun i => (cAffine (Matrix.of fun i j => v j i) x w i).re) :=
    continuous_pi fun i =>
      Complex.continuous_re.comp ((continuous_apply i).comp hcont_aff)
  have hA_open : IsOpen {w : Fin n → ℂ |
      (fun i => (cAffine (Matrix.of fun i j => v j i) x w i).re) ∈ U} :=
    IsOpen.preimage hre_cont hU_open
  have h0 : (0 : Fin n → ℂ) ∈ {w : Fin n → ℂ |
      (fun i => (cAffine (Matrix.of fun i j => v j i) x w i).re) ∈ U} := by
    change (fun i => (cAffine (Matrix.of fun i j => v j i) x 0 i).re) ∈ U
    rw [cAffine_re]
    have hz : (fun j : Fin n => ((0 : Fin n → ℂ) j).re) = 0 := by
      ext j; simp
    rw [hz, Matrix.mulVec_zero, add_zero]
    exact hx_U
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hA_open 0 h0
  refine ⟨ρ, hρ, ?_, ?_, ?_⟩
  · have hmaps : Set.MapsTo (cAffine (Matrix.of fun i j => v j i) x)
        (Metric.ball 0 ρ ∩ TubeDomain (PosOrthant n)) (TubeDomain V_plus) :=
      fun w hw => cAffine_mem_tube_plus hn hV_plus_convex hV_plus_cone v hv x w hw.2
    exact h_holo_plus.comp (differentiable_cAffine _ x).differentiableOn hmaps
  · have hmaps : Set.MapsTo (cAffine (Matrix.of fun i j => v j i) x)
        (Metric.ball 0 ρ ∩ TubeDomain (NegOrthant n))
        (TubeDomain ((fun v : Fin n → ℝ => -v) '' V_plus)) :=
      fun w hw => cAffine_mem_tube_minus hn hV_plus_convex hV_plus_cone v hv x w hw.2
    exact h_holo_minus.comp (differentiable_cAffine _ x).differentiableOn hmaps
  · have hmaps : Set.MapsTo (cAffine (Matrix.of fun i j => v j i) x)
        (Metric.ball 0 ρ ∩
          (TubeDomain (PosOrthant n) ∪ TubeDomain (NegOrthant n) ∪
            {w : Fin n → ℂ | ∀ i, (w i).im = 0}))
        (WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U) := by
      intro w hw
      obtain ⟨hwb, hw'⟩ := hw
      rcases hw' with (hp | hm) | hr
      · exact Or.inl (Or.inl (cAffine_mem_tube_plus hn hV_plus_convex hV_plus_cone v hv x w hp))
      · exact Or.inl (Or.inr (cAffine_mem_tube_minus hn hV_plus_convex hV_plus_cone v hv x w hm))
      · refine Or.inr ⟨hball hwb, ?_⟩
        rw [cAffine_im]
        have hzero : (fun j => (w j).im) = 0 := by
          ext j; exact hr j
        rw [hzero, Matrix.mulVec_zero]
    exact h_cont.comp hcont_aff.continuousOn hmaps

lemma orthant_eowData_bounded_on_compact (n : ℕ)
    (g : (Fin n → ℂ) → ℂ) (ρ : ℝ) (hdata : OrthantEOWData n g ρ)
    (K : Set (Fin n → ℂ)) (hK : IsCompact K)
    (hK_sub : K ⊆ Metric.ball 0 ρ ∩
      (TubeDomain (PosOrthant n) ∪ TubeDomain (NegOrthant n) ∪
        {w : Fin n → ℂ | ∀ i, (w i).im = 0})) :
    ∃ M : ℝ, ∀ w ∈ K, ‖g w‖ ≤ M := by
  have hcont : ContinuousOn g K := hdata.2.2.mono hK_sub
  have h_img : IsCompact (g '' K) := hK.image_of_continuousOn hcont
  rcases h_img.isBounded.exists_norm_le with ⟨M, hM⟩
  refine ⟨M, fun w hw => ?_⟩
  exact hM (g w) (mem_image_of_mem g hw)

noncomputable def diagCLM (n : ℕ) : ℂ →L[ℂ] (Fin n → ℂ) :=
  ContinuousLinearMap.pi fun _ => ContinuousLinearMap.id ℂ ℂ

lemma diagCLM_apply (n : ℕ) (t : ℂ) (i : Fin n) :
    diagCLM n t i = t := rfl

lemma diagCLM_mem_ball (n : ℕ) {ρ : ℝ} {t : ℂ} (ht : t ∈ Metric.ball 0 ρ) :
    diagCLM n t ∈ Metric.ball (0 : Fin n → ℂ) ρ := by
  rcases le_or_gt ρ 0 with hρ | hρ
  · have : ¬ (t ∈ Metric.ball (0 : ℂ) ρ) := by
      rw [Metric.mem_ball]
      intro h
      have := lt_of_le_of_lt dist_nonneg h
      linarith
    contradiction
  · rw [Metric.mem_ball]
    apply (dist_pi_lt_iff hρ).mpr
    intro i
    dsimp [diagCLM]
    exact Metric.mem_ball.mp ht

lemma diagCLM_mem_posOrthant (n : ℕ) {t : ℂ} (ht : 0 < t.im) :
    diagCLM n t ∈ TubeDomain (PosOrthant n) := by
  intro i
  simpa [diagCLM_apply] using ht

lemma diagCLM_mem_negOrthant (n : ℕ) {t : ℂ} (ht : t.im < 0) :
    diagCLM n t ∈ TubeDomain (NegOrthant n) := by
  intro i
  simpa [diagCLM_apply] using ht

lemma diagCLM_im_zero (n : ℕ) {t : ℂ} (ht : t.im = 0) :
    ∀ i, (diagCLM n t i).im = 0 := by
  intro i
  simpa [diagCLM_apply] using ht

lemma orthant_eowData_diag_diff_upper (n : ℕ)
    (g : (Fin n → ℂ) → ℂ) (ρ : ℝ) (hdata : OrthantEOWData n g ρ) :
    DifferentiableOn ℂ (g ∘ diagCLM n) (Metric.ball 0 ρ ∩ upperHalfPlane) := by
  have hmaps : Set.MapsTo (diagCLM n) (Metric.ball 0 ρ ∩ upperHalfPlane)
      (Metric.ball 0 ρ ∩ TubeDomain (PosOrthant n)) := by
    intro t ht
    exact ⟨diagCLM_mem_ball n ht.1, diagCLM_mem_posOrthant n ht.2⟩
  exact hdata.1.comp (diagCLM n).differentiable.differentiableOn hmaps

lemma orthant_eowData_diag_diff_lower (n : ℕ)
    (g : (Fin n → ℂ) → ℂ) (ρ : ℝ) (hdata : OrthantEOWData n g ρ) :
    DifferentiableOn ℂ (g ∘ diagCLM n) (Metric.ball 0 ρ ∩ lowerHalfPlane) := by
  have hmaps : Set.MapsTo (diagCLM n) (Metric.ball 0 ρ ∩ lowerHalfPlane)
      (Metric.ball 0 ρ ∩ TubeDomain (NegOrthant n)) := by
    intro t ht
    exact ⟨diagCLM_mem_ball n ht.1, diagCLM_mem_negOrthant n ht.2⟩
  exact hdata.2.1.comp (diagCLM n).differentiable.differentiableOn hmaps

lemma orthant_eowData_diag_continuousOn (n : ℕ)
    (g : (Fin n → ℂ) → ℂ) (ρ : ℝ) (hdata : OrthantEOWData n g ρ) :
    ContinuousOn (g ∘ diagCLM n)
      (Metric.ball 0 ρ ∩ (upperHalfPlane ∪ lowerHalfPlane ∪ {t : ℂ | t.im = 0})) := by
  have hmaps : Set.MapsTo (diagCLM n)
      (Metric.ball 0 ρ ∩ (upperHalfPlane ∪ lowerHalfPlane ∪ {t : ℂ | t.im = 0}))
      (Metric.ball 0 ρ ∩
        (TubeDomain (PosOrthant n) ∪ TubeDomain (NegOrthant n) ∪
          {w : Fin n → ℂ | ∀ i, (w i).im = 0})) := by
    intro t ht
    refine ⟨diagCLM_mem_ball n ht.1, ?_⟩
    rcases ht.2 with (hp | hm) | hr
    · exact Or.inl (Or.inl (diagCLM_mem_posOrthant n hp))
    · exact Or.inl (Or.inr (diagCLM_mem_negOrthant n hm))
    · exact Or.inr (diagCLM_im_zero n hr)
  exact hdata.2.2.comp (diagCLM n).continuous.continuousOn hmaps

lemma bogoliubov_partial_fraction (ζ₀ ζ₁ w₀ w₁ : ℂ)
    (h0 : ζ₀ - w₀ ≠ 0) (h1 : ζ₁ - w₁ ≠ 0)
    (h_diff : (w₀ - w₁) - (ζ₀ - ζ₁) ≠ 0) :
    (ζ₀ - w₀)⁻¹ * (ζ₁ - w₁)⁻¹ =
      ((w₀ - w₁) - (ζ₀ - ζ₁))⁻¹ * ((ζ₀ - w₀)⁻¹ - (ζ₁ - w₁)⁻¹) := by
  have heq : ((w₀ - w₁) - (ζ₀ - ζ₁)) = (ζ₁ - w₁) - (ζ₀ - w₀) := by ring
  rw [heq] at h_diff ⊢
  have h_sub : (ζ₀ - w₀)⁻¹ - (ζ₁ - w₁)⁻¹ =
      ((ζ₁ - w₁) - (ζ₀ - w₀)) * ((ζ₀ - w₀)⁻¹ * (ζ₁ - w₁)⁻¹) := by
    field_simp
  rw [h_sub, ← mul_assoc, inv_mul_cancel₀ h_diff, one_mul]

lemma analyticAt_bogoliubov_kernel (ζ₀ ζ₁ : ℂ) (w : Fin 2 → ℂ)
    (h0 : ζ₀ - w 0 ≠ 0) (h1 : ζ₁ - w 1 ≠ 0)
    (h_diff : (w 0 - w 1) - (ζ₀ - ζ₁) ≠ 0) :
    AnalyticAt ℂ (fun u : Fin 2 → ℂ =>
      ((u 0 - u 1) - (ζ₀ - ζ₁))⁻¹ * ((ζ₀ - u 0)⁻¹ - (ζ₁ - u 1)⁻¹)) w := by
  let P0 : (Fin 2 → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj 0
  let P1 : (Fin 2 → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj 1
  have hP0 : AnalyticAt ℂ P0 w := P0.analyticAt w
  have hP1 : AnalyticAt ℂ P1 w := P1.analyticAt w
  have han_diff : AnalyticAt ℂ (fun u : Fin 2 → ℂ => ((u 0 - u 1) - (ζ₀ - ζ₁))) w := by
    change AnalyticAt ℂ (fun u => P0 u - P1 u - (ζ₀ - ζ₁)) w
    exact (hP0.sub hP1).sub analyticAt_const
  have han_diff_inv : AnalyticAt ℂ (fun u : Fin 2 → ℂ => ((u 0 - u 1) - (ζ₀ - ζ₁))⁻¹) w :=
    han_diff.inv h_diff
  have han0 : AnalyticAt ℂ (fun u : Fin 2 → ℂ => (ζ₀ - u 0)⁻¹) w := by
    have h : AnalyticAt ℂ (fun u => ζ₀ - P0 u) w := analyticAt_const.sub hP0
    exact h.inv h0
  have han1 : AnalyticAt ℂ (fun u : Fin 2 → ℂ => (ζ₁ - u 1)⁻¹) w := by
    have h : AnalyticAt ℂ (fun u => ζ₁ - P1 u) w := analyticAt_const.sub hP1
    exact h.inv h1
  exact han_diff_inv.mul (han0.sub han1)

lemma analyticAt_cauchy_prod_via_bogoliubov (ζ₀ ζ₁ : ℂ) (w : Fin 2 → ℂ)
    (h0 : ζ₀ - w 0 ≠ 0) (h1 : ζ₁ - w 1 ≠ 0)
    (h_diff : (w 0 - w 1) - (ζ₀ - ζ₁) ≠ 0) :
    AnalyticAt ℂ (fun u : Fin 2 → ℂ => (ζ₀ - u 0)⁻¹ * (ζ₁ - u 1)⁻¹) w := by
  have h_bog := analyticAt_bogoliubov_kernel ζ₀ ζ₁ w h0 h1 h_diff
  have h_open : IsOpen
      {u : Fin 2 → ℂ | ζ₀ - u 0 ≠ 0 ∧ ζ₁ - u 1 ≠ 0 ∧ (u 0 - u 1) - (ζ₀ - ζ₁) ≠ 0} := by
    let P0 : (Fin 2 → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj 0
    let P1 : (Fin 2 → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj 1
    have h1_op : IsOpen {u : Fin 2 → ℂ | ζ₀ - u 0 ≠ 0} :=
      isOpen_ne.preimage (continuous_const.sub P0.continuous)
    have h2_op : IsOpen {u : Fin 2 → ℂ | ζ₁ - u 1 ≠ 0} :=
      isOpen_ne.preimage (continuous_const.sub P1.continuous)
    have h3_op : IsOpen {u : Fin 2 → ℂ | (u 0 - u 1) - (ζ₀ - ζ₁) ≠ 0} :=
      isOpen_ne.preimage ((P0.continuous.sub P1.continuous).sub continuous_const)
    exact h1_op.inter (h2_op.inter h3_op)
  have hw_mem : w ∈ {u : Fin 2 → ℂ | ζ₀ - u 0 ≠ 0 ∧ ζ₁ - u 1 ≠ 0 ∧ (u 0 - u 1) - (ζ₀ - ζ₁) ≠ 0} :=
    ⟨h0, h1, h_diff⟩
  have h_ev : (fun u : Fin 2 → ℂ => ((u 0 - u 1) - (ζ₀ - ζ₁))⁻¹ * ((ζ₀ - u 0)⁻¹ - (ζ₁ - u 1)⁻¹))
      =ᶠ[nhds w] (fun u : Fin 2 → ℂ => (ζ₀ - u 0)⁻¹ * (ζ₁ - u 1)⁻¹) := by
    apply Filter.eventuallyEq_iff_exists_mem.mpr
    refine ⟨_, h_open.mem_nhds hw_mem, ?_⟩
    intro u hu
    exact (bogoliubov_partial_fraction ζ₀ ζ₁ (u 0) (u 1) hu.1 hu.2.1 hu.2.2).symm
  exact h_bog.congr h_ev

noncomputable def diagMeanCLM2 : (Fin 2 → ℂ) →L[ℂ] ℂ :=
  (1/2 : ℂ) • ((ContinuousLinearMap.proj (0 : Fin 2) : (Fin 2 → ℂ) →L[ℂ] ℂ) +
               (ContinuousLinearMap.proj (1 : Fin 2) : (Fin 2 → ℂ) →L[ℂ] ℂ))

noncomputable def transverseDiffCLM2 : (Fin 2 → ℂ) →L[ℂ] ℂ :=
  (1/2 : ℂ) • ((ContinuousLinearMap.proj (0 : Fin 2) : (Fin 2 → ℂ) →L[ℂ] ℂ) -
               (ContinuousLinearMap.proj (1 : Fin 2) : (Fin 2 → ℂ) →L[ℂ] ℂ))

lemma diagMeanCLM2_apply (w : Fin 2 → ℂ) :
    diagMeanCLM2 w = (w 0 + w 1) / 2 := by
  change (1/2 : ℂ) * (w 0 + w 1) = (w 0 + w 1) / 2
  ring

lemma transverseDiffCLM2_apply (w : Fin 2 → ℂ) :
    transverseDiffCLM2 w = (w 0 - w 1) / 2 := by
  change (1/2 : ℂ) * (w 0 - w 1) = (w 0 - w 1) / 2
  ring

lemma coord_reconstruction (w : Fin 2 → ℂ) :
    w 0 = diagMeanCLM2 w + transverseDiffCLM2 w ∧
    w 1 = diagMeanCLM2 w - transverseDiffCLM2 w := by
  simp only [diagMeanCLM2_apply, transverseDiffCLM2_apply]
  constructor <;> ring

lemma norm_half_c : ‖(1/2 : ℂ)‖ = (1/2 : ℝ) := by
  norm_num

lemma diagMeanCLM2_mem_ball {ρ : ℝ} {w : Fin 2 → ℂ} (hw : w ∈ Metric.ball 0 ρ) :
    diagMeanCLM2 w ∈ Metric.ball (0 : ℂ) ρ := by
  rw [Metric.mem_ball] at hw ⊢
  have h0 : ‖w 0‖ < ρ := by
    rw [← dist_zero_right]
    exact lt_of_le_of_lt (dist_le_pi_dist w 0 0) hw
  have h1 : ‖w 1‖ < ρ := by
    rw [← dist_zero_right]
    exact lt_of_le_of_lt (dist_le_pi_dist w 0 1) hw
  rw [diagMeanCLM2_apply, dist_zero_right]
  calc ‖(w 0 + w 1) / 2‖
    _ = ‖(w 0 + w 1) * (1/2 : ℂ)‖ := by ring_nf
    _ = ‖w 0 + w 1‖ * ‖(1/2 : ℂ)‖ := norm_mul _ _
    _ = ‖w 0 + w 1‖ * (1/2) := by rw [norm_half_c]
    _ ≤ (‖w 0‖ + ‖w 1‖) * (1/2) := by gcongr; exact norm_add_le (w 0) (w 1)
    _ < (ρ + ρ) * (1/2) := by gcongr
    _ = ρ := by ring

lemma transverseDiffCLM2_mem_ball {ρ : ℝ} {w : Fin 2 → ℂ} (hw : w ∈ Metric.ball 0 ρ) :
    transverseDiffCLM2 w ∈ Metric.ball (0 : ℂ) ρ := by
  rw [Metric.mem_ball] at hw ⊢
  have h0 : ‖w 0‖ < ρ := by
    rw [← dist_zero_right]
    exact lt_of_le_of_lt (dist_le_pi_dist w 0 0) hw
  have h1 : ‖w 1‖ < ρ := by
    rw [← dist_zero_right]
    exact lt_of_le_of_lt (dist_le_pi_dist w 0 1) hw
  rw [transverseDiffCLM2_apply, dist_zero_right]
  calc ‖(w 0 - w 1) / 2‖
    _ = ‖(w 0 - w 1) * (1/2 : ℂ)‖ := by ring_nf
    _ = ‖w 0 - w 1‖ * ‖(1/2 : ℂ)‖ := norm_mul _ _
    _ = ‖w 0 - w 1‖ * (1/2) := by rw [norm_half_c]
    _ ≤ (‖w 0‖ + ‖w 1‖) * (1/2) := by
      gcongr
      exact norm_sub_le (w 0) (w 1)
    _ < (ρ + ρ) * (1/2) := by gcongr
    _ = ρ := by ring

lemma circleIntegrable_of_continuous {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (h_cont : ContinuousOn f (Metric.sphere c |R|)) :
    CircleIntegrable f c R :=
  ContinuousOn.circleIntegrable' h_cont

lemma continuousOn_cauchy_kernel {w c : ℂ} {R : ℝ}
    (hw : w ∉ Metric.sphere c |R|) :
    ContinuousOn (fun ζ => (ζ - w)⁻¹) (Metric.sphere c |R|) := by
  refine ContinuousOn.inv₀ ?_ ?_
  · exact continuous_id.continuousOn.sub continuousOn_const
  · intro ζ hζ h_eq
    have : ζ = w := sub_eq_zero.mp h_eq
    subst this
    exact hw hζ

lemma circleIntegrable_cauchy_kernel {w c : ℂ} {R : ℝ}
    (hw : w ∉ Metric.sphere c |R|) :
    CircleIntegrable (fun ζ => (ζ - w)⁻¹) c R :=
  circleIntegrable_of_continuous (continuousOn_cauchy_kernel hw)

noncomputable def diagTransCLM2 : (ℂ × ℂ) →L[ℂ] (Fin 2 → ℂ) :=
  ContinuousLinearMap.pi fun i =>
    if i = 0 then
      (ContinuousLinearMap.fst ℂ ℂ ℂ) + (ContinuousLinearMap.snd ℂ ℂ ℂ)
    else
      (ContinuousLinearMap.fst ℂ ℂ ℂ) - (ContinuousLinearMap.snd ℂ ℂ ℂ)

lemma diagTransCLM2_apply (p : ℂ × ℂ) (i : Fin 2) :
    diagTransCLM2 p i = if i = 0 then p.1 + p.2 else p.1 - p.2 := by
  simp only [diagTransCLM2, ContinuousLinearMap.pi_apply]
  split_ifs <;> rfl

lemma diagTransCLM2_apply_zero (p : ℂ × ℂ) :
    diagTransCLM2 p 0 = p.1 + p.2 := by
  rw [diagTransCLM2_apply]
  simp

lemma diagTransCLM2_apply_one (p : ℂ × ℂ) :
    diagTransCLM2 p 1 = p.1 - p.2 := by
  rw [diagTransCLM2_apply]
  simp

lemma diagTrans_reconstruction (w : Fin 2 → ℂ) :
    diagTransCLM2 (diagMeanCLM2 w, transverseDiffCLM2 w) = w := by
  ext i
  rw [diagTransCLM2_apply]
  fin_cases i
  · simp [(coord_reconstruction w).1.symm]
  · simp [(coord_reconstruction w).2.symm]

lemma diagMean_diagTrans (u v : ℂ) :
    diagMeanCLM2 (diagTransCLM2 (u, v)) = u := by
  rw [diagMeanCLM2_apply, diagTransCLM2_apply_zero, diagTransCLM2_apply_one]
  ring

lemma transverseDiff_diagTrans (u v : ℂ) :
    transverseDiffCLM2 (diagTransCLM2 (u, v)) = v := by
  rw [transverseDiffCLM2_apply, diagTransCLM2_apply_zero, diagTransCLM2_apply_one]
  ring

lemma diagTrans_im_zero (u v : ℂ) :
    (diagTransCLM2 (u, v) 0).im = u.im + v.im := by
  rw [diagTransCLM2_apply_zero, Complex.add_im]

lemma diagTrans_im_one (u v : ℂ) :
    (diagTransCLM2 (u, v) 1).im = u.im - v.im := by
  rw [diagTransCLM2_apply_one, Complex.sub_im]

lemma diagTrans_mem_posOrthant (u : ℂ) (v : ℂ) (hv : v.im = 0) (hu : 0 < u.im) :
    diagTransCLM2 (u, v) ∈ TubeDomain (PosOrthant 2) := by
  intro i
  dsimp
  rw [diagTransCLM2_apply]
  fin_cases i
  · simp [hv, hu]
  · simp [hv, hu]

lemma diagTrans_mem_negOrthant (u : ℂ) (v : ℂ) (hv : v.im = 0) (hu : u.im < 0) :
    diagTransCLM2 (u, v) ∈ TubeDomain (NegOrthant 2) := by
  intro i
  dsimp
  rw [diagTransCLM2_apply]
  fin_cases i
  · simp [hv, hu]
  · simp [hv, hu]

lemma diagTrans_im_both_zero (u : ℂ) (v : ℂ) (hu : u.im = 0) (hv : v.im = 0) :
    ∀ i, (diagTransCLM2 (u, v) i).im = 0 := by
  intro i
  rw [diagTransCLM2_apply]
  fin_cases i
  · simp [hu, hv]
  · simp [hu, hv]

lemma diagTrans_mem_ball {u v : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hu : ‖u‖ < ρ / 2) (hv : ‖v‖ < ρ / 2) :
    diagTransCLM2 (u, v) ∈ Metric.ball (0 : Fin 2 → ℂ) ρ := by
  rw [Metric.mem_ball, dist_zero_right]
  apply (pi_norm_lt_iff hρ).mpr
  intro i
  rw [diagTransCLM2_apply]
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, ↓reduceIte]
    calc ‖u + v‖ ≤ ‖u‖ + ‖v‖ := norm_add_le u v
      _ < ρ / 2 + ρ / 2 := add_lt_add hu hv
      _ = ρ := add_halves ρ
  · simp only [Fin.mk_one, Fin.isValue, one_ne_zero, ↓reduceIte]
    calc ‖u - v‖ ≤ ‖u‖ + ‖v‖ := norm_sub_le u v
      _ < ρ / 2 + ρ / 2 := add_lt_add hu hv
      _ = ρ := add_halves ρ

lemma differentiable_diagTrans_left (v : ℂ) :
    Differentiable ℂ (fun (u : ℂ) => diagTransCLM2 (u, v)) := by
  have hd : Differentiable ℂ (fun (u : ℂ) => (u, v)) :=
    (differentiable_id : Differentiable ℂ (fun u : ℂ => u)).prodMk (differentiable_const v)
  exact diagTransCLM2.differentiable.comp hd

lemma diagTrans_slice_diff_upper (g : (Fin 2 → ℂ) → ℂ) {ρ : ℝ} (hρ : 0 < ρ)
    (hdata : OrthantEOWData 2 g ρ) (v : ℂ) (hv : v.im = 0) (hv_norm : ‖v‖ < ρ / 2) :
    DifferentiableOn ℂ (fun u => g (diagTransCLM2 (u, v)))
      (Metric.ball (0 : ℂ) (ρ / 2) ∩ upperHalfPlane) := by
  have hmaps : Set.MapsTo (fun u => diagTransCLM2 (u, v))
      (Metric.ball (0 : ℂ) (ρ / 2) ∩ upperHalfPlane)
      (Metric.ball 0 ρ ∩ TubeDomain (PosOrthant 2)) := by
    intro u hu
    refine ⟨diagTrans_mem_ball hρ (by simpa using hu.1) hv_norm, ?_⟩
    exact diagTrans_mem_posOrthant u v hv hu.2
  exact hdata.1.comp (differentiable_diagTrans_left v).differentiableOn hmaps

lemma diagTrans_slice_diff_lower (g : (Fin 2 → ℂ) → ℂ) {ρ : ℝ} (hρ : 0 < ρ)
    (hdata : OrthantEOWData 2 g ρ) (v : ℂ) (hv : v.im = 0) (hv_norm : ‖v‖ < ρ / 2) :
    DifferentiableOn ℂ (fun u => g (diagTransCLM2 (u, v)))
      (Metric.ball (0 : ℂ) (ρ / 2) ∩ lowerHalfPlane) := by
  have hmaps : Set.MapsTo (fun u => diagTransCLM2 (u, v))
      (Metric.ball (0 : ℂ) (ρ / 2) ∩ lowerHalfPlane)
      (Metric.ball 0 ρ ∩ TubeDomain (NegOrthant 2)) := by
    intro u hu
    refine ⟨diagTrans_mem_ball hρ (by simpa using hu.1) hv_norm, ?_⟩
    exact diagTrans_mem_negOrthant u v hv hu.2
  exact hdata.2.1.comp (differentiable_diagTrans_left v).differentiableOn hmaps

lemma diagTrans_slice_continuousOn (g : (Fin 2 → ℂ) → ℂ) {ρ : ℝ} (hρ : 0 < ρ)
    (hdata : OrthantEOWData 2 g ρ) (v : ℂ) (hv : v.im = 0) (hv_norm : ‖v‖ < ρ / 2) :
    ContinuousOn (fun u => g (diagTransCLM2 (u, v)))
      (Metric.ball (0 : ℂ) (ρ / 2) ∩ (upperHalfPlane ∪ lowerHalfPlane ∪ {t : ℂ | t.im = 0})) := by
  have hmaps : Set.MapsTo (fun u => diagTransCLM2 (u, v))
      (Metric.ball (0 : ℂ) (ρ / 2) ∩ (upperHalfPlane ∪ lowerHalfPlane ∪ {t : ℂ | t.im = 0}))
      (Metric.ball 0 ρ ∩
        (TubeDomain (PosOrthant 2) ∪ TubeDomain (NegOrthant 2) ∪
          {w : Fin 2 → ℂ | ∀ i, (w i).im = 0})) := by
    intro u hu
    refine ⟨diagTrans_mem_ball hρ (by simpa using hu.1) hv_norm, ?_⟩
    rcases hu.2 with (h_up | h_low) | h_real
    · exact Or.inl (Or.inl (diagTrans_mem_posOrthant u v hv h_up))
    · exact Or.inl (Or.inr (diagTrans_mem_negOrthant u v hv h_low))
    · exact Or.inr (diagTrans_im_both_zero u v h_real hv)
  exact hdata.2.2.comp (differentiable_diagTrans_left v).continuous.continuousOn hmaps

lemma diagTrans_zero_eq_diag (u : ℂ) :
    diagTransCLM2 (u, 0) = fun _ => u := by
  ext i
  rw [diagTransCLM2_apply]
  fin_cases i
  · simp
  · simp

noncomputable def diagCauchy1 (g : (Fin 2 → ℂ) → ℂ) (R : ℝ) (u : ℂ) : ℂ :=
  (2 * Real.pi * Complex.I : ℂ)⁻¹ • ∮ ζ in C(0, R), (ζ - u)⁻¹ • g (fun _ => ζ)

lemma analyticAt_diagCauchy1 (g : (Fin 2 → ℂ) → ℂ) {R : ℝ} (hR : 0 < R)
    (h_int : CircleIntegrable (fun ζ => g (fun _ => ζ)) 0 R)
    {u : ℂ} (hu : u ∈ Metric.ball 0 R) :
    AnalyticAt ℂ (diagCauchy1 g R) u := by
  lift R to NNReal using hR.le with R_nn
  have hu' : u ∈ Metric.eball 0 R_nn := by
    rw [Metric.eball_coe]
    exact hu
  have h_series := hasFPowerSeriesOn_cauchy_integral h_int hR
  exact h_series.analyticAt_of_mem hu'

lemma circleIntegrable_diagSlice (g : (Fin 2 → ℂ) → ℂ) {ρ : ℝ} (_hρ : 0 < ρ)
    (hdata : OrthantEOWData 2 g ρ) {R : ℝ} (hR_pos : 0 < R) (hR_lt : R < ρ) :
    CircleIntegrable (fun ζ => g (fun _ => ζ)) 0 R := by
  have hmaps : Set.MapsTo (fun ζ : ℂ => (fun _ : Fin 2 => ζ))
      (Metric.sphere (0 : ℂ) |R|)
      (Metric.ball 0 ρ ∩ (TubeDomain (PosOrthant 2) ∪ TubeDomain (NegOrthant 2) ∪
        {w : Fin 2 → ℂ | ∀ i, (w i).im = 0})) := by
    intro ζ hζ
    rw [Metric.mem_sphere, dist_zero_right] at hζ
    have hζ_ball : (fun _ : Fin 2 => ζ) ∈ Metric.ball (0 : Fin 2 → ℂ) ρ := by
      rw [Metric.mem_ball, dist_zero_right]
      apply (pi_norm_lt_iff (by linarith)).mpr
      intro i
      rw [hζ, abs_of_pos hR_pos]
      exact hR_lt
    refine ⟨hζ_ball, ?_⟩
    rcases lt_trichotomy (0 : ℝ) ζ.im with h_pos | h_zero | h_neg
    · left; left
      intro i; exact h_pos
    · right
      intro i; exact h_zero.symm
    · left; right
      intro i; exact h_neg
  have h_cont_sphere : ContinuousOn (fun ζ => g (fun _ => ζ)) (Metric.sphere 0 |R|) := by
    have hd_cont : Continuous (fun ζ : ℂ => (fun _ : Fin 2 => ζ)) :=
      continuous_pi fun _ => continuous_id
    exact hdata.2.2.comp hd_cont.continuousOn hmaps
  exact circleIntegrable_of_continuous h_cont_sphere

lemma diagCauchy1_eq_of_differentiableOn
    (g : (Fin 2 → ℂ) → ℂ) {R : ℝ} (_hR : 0 < R)
    (h_diff : DifferentiableOn ℂ (fun ζ => g (fun _ => ζ)) (Metric.closedBall 0 R))
    {u : ℂ} (hu : u ∈ Metric.ball 0 R) :
    diagCauchy1 g R u = g (fun _ => u) := by
  have h_cauchy := DifferentiableOn.circleIntegral_sub_inv_smul h_diff hu
  have h_2piI_ne : (2 * ↑Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Complex.I_ne_zero, Real.pi_ne_zero]
  change (2 * ↑Real.pi * Complex.I : ℂ)⁻¹ • ∮ ζ in C(0, R), (ζ - u)⁻¹ • g (fun _ => ζ) = _
  rw [h_cauchy, ← mul_smul, inv_mul_cancel₀ h_2piI_ne, one_smul]

noncomputable def eowAnalyticKernel2 (g : (Fin 2 → ℂ) → ℂ) (R : ℝ) (w : Fin 2 → ℂ) : ℂ :=
  (2 * Real.pi * Complex.I : ℂ)⁻¹ •
    ∮ ζ in C(0, R), (ζ - diagMeanCLM2 w)⁻¹ • g (diagTransCLM2 (ζ, transverseDiffCLM2 w))

theorem eowAnalyticKernel2_eq_of_differentiableOn
    (g : (Fin 2 → ℂ) → ℂ) {R : ℝ} (_hR : 0 < R)
    (w : Fin 2 → ℂ)
    (h_diff : DifferentiableOn ℂ (fun ζ => g (diagTransCLM2 (ζ, transverseDiffCLM2 w)))
      (Metric.closedBall 0 R))
    (hw_mean : diagMeanCLM2 w ∈ Metric.ball 0 R) :
    eowAnalyticKernel2 g R w = g w := by
  have h_cauchy := DifferentiableOn.circleIntegral_sub_inv_smul h_diff hw_mean
  have h_2piI_ne : (2 * ↑Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Complex.I_ne_zero, Real.pi_ne_zero]
  change (2 * ↑Real.pi * Complex.I : ℂ)⁻¹ • ∮ ζ in C(0, R),
    (ζ - diagMeanCLM2 w)⁻¹ • g (diagTransCLM2 (ζ, transverseDiffCLM2 w)) = _
  rw [h_cauchy, ← mul_smul, inv_mul_cancel₀ h_2piI_ne, one_smul]
  exact congr_arg g (diagTrans_reconstruction w)

lemma analyticOnNhd_diagMean_comp (G1 : ℂ → ℂ) {ρ : ℝ}
    (hG1 : AnalyticOnNhd ℂ G1 (Metric.ball 0 ρ)) :
    AnalyticOnNhd ℂ (G1 ∘ diagMeanCLM2) (Metric.ball (0 : Fin 2 → ℂ) ρ) := by
  intro w hw
  have hw_mean := diagMeanCLM2_mem_ball hw
  exact (hG1 (diagMeanCLM2 w) hw_mean).comp (diagMeanCLM2.analyticAt w)

lemma orthant_eow_core_of_an (n : ℕ) (g : (Fin n → ℂ) → ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (G : (Fin n → ℂ) → ℂ) (hG_an : AnalyticOnNhd ℂ G (Metric.ball 0 ρ))
    (W₁ : Set (Fin n → ℂ)) (hW₁_open : IsOpen W₁) (hW₁_ne : W₁.Nonempty)
    (hW₁_sub : W₁ ⊆ Metric.ball 0 ρ ∩ TubeDomain (PosOrthant n)) (hG_eq1 : EqOn G g W₁)
    (W₂ : Set (Fin n → ℂ)) (hW₂_open : IsOpen W₂) (hW₂_ne : W₂.Nonempty)
    (hW₂_sub : W₂ ⊆ Metric.ball 0 ρ ∩ TubeDomain (NegOrthant n)) (hG_eq2 : EqOn G g W₂) :
    OrthantEOWCore n g :=
  ⟨ρ, hρ, G, hG_an,
    ⟨W₁, hW₁_open, hW₁_ne, hW₁_sub, hG_eq1⟩, ⟨W₂, hW₂_open, hW₂_ne, hW₂_sub, hG_eq2⟩⟩

noncomputable def polyKernel2 (a : Fin 2 → ℕ) (t : Fin 2 → ℝ) (z : Fin 2 → ℂ) : ℂ :=
  (z 0 - (t 0 : ℂ))^(a 0) * (z 1 - (t 1 : ℂ))^(a 1)

lemma polyKernel2_analyticAt (a : Fin 2 → ℕ) (t : Fin 2 → ℝ) (z : Fin 2 → ℂ) :
    AnalyticAt ℂ (polyKernel2 a t) z := by
  unfold polyKernel2
  let p0 : (Fin 2 → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj 0
  let p1 : (Fin 2 → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj 1
  have han0 : AnalyticAt ℂ (fun w => (w 0 - (t 0 : ℂ))^(a 0)) z := by
    have h1 : AnalyticAt ℂ (fun w => p0 w - (t 0 : ℂ)) z := (p0.analyticAt z).sub analyticAt_const
    exact h1.pow (a 0)
  have han1 : AnalyticAt ℂ (fun w => (w 1 - (t 1 : ℂ))^(a 1)) z := by
    have h1 : AnalyticAt ℂ (fun w => p1 w - (t 1 : ℂ)) z := (p1.analyticAt z).sub analyticAt_const
    exact h1.pow (a 1)
  exact han0.mul han1

noncomputable def polyMollifier2 (a : Fin 2 → ℕ) (t : Fin 2 → ℝ) (c : ℂ) (z : Fin 2 → ℂ) : ℂ :=
  c * polyKernel2 a t z

theorem polyMollifier2_analyticOnNhd (a : Fin 2 → ℕ) (t : Fin 2 → ℝ) (c : ℂ) (R : ℝ) :
    AnalyticOnNhd ℂ (polyMollifier2 a t c) (Metric.ball 0 R) := by
  intro z _hz
  unfold polyMollifier2
  exact analyticAt_const.mul (polyKernel2_analyticAt a t z)

theorem orthant_eow_core_2d_mollified
    (a : Fin 2 → ℕ) (t : Fin 2 → ℝ) (c : ℂ) (R : ℝ) (hR_pos : 0 < R) :
    OrthantEOWCore 2 (polyMollifier2 a t c) := by
  let G := polyMollifier2 a t c
  have hG_an : AnalyticOnNhd ℂ G (Metric.ball 0 R) :=
    polyMollifier2_analyticOnNhd a t c R
  obtain ⟨z₁, hz₁_b, hz₁_pos⟩ := posOrthant_ball_inter_nonempty 2 R hR_pos
  obtain ⟨z₂, hz₂_b, hz₂_neg⟩ := negOrthant_ball_inter_nonempty 2 R hR_pos
  have hB_open : IsOpen (Metric.ball (0 : Fin 2 → ℂ) R) := Metric.isOpen_ball
  have hPos_open : IsOpen (TubeDomain (PosOrthant 2)) := isOpen_TubeDomain (isOpen_PosOrthant 2)
  have hNeg_open : IsOpen (TubeDomain (NegOrthant 2)) := isOpen_TubeDomain (isOpen_NegOrthant 2)
  have h_open1 : IsOpen (Metric.ball 0 R ∩ TubeDomain (PosOrthant 2)) := hB_open.inter hPos_open
  have h_open2 : IsOpen (Metric.ball 0 R ∩ TubeDomain (NegOrthant 2)) := hB_open.inter hNeg_open
  have h_ne1 : (Metric.ball 0 R ∩ TubeDomain (PosOrthant 2)).Nonempty := ⟨z₁, hz₁_b, hz₁_pos⟩
  have h_ne2 : (Metric.ball 0 R ∩ TubeDomain (NegOrthant 2)).Nonempty := ⟨z₂, hz₂_b, hz₂_neg⟩
  refine ⟨R, hR_pos, G, hG_an, ?_, ?_⟩
  · refine ⟨Metric.ball 0 R ∩ TubeDomain (PosOrthant 2), h_open1, h_ne1, subset_rfl, ?_⟩
    intro _w _hw
    rfl
  · refine ⟨Metric.ball 0 R ∩ TubeDomain (NegOrthant 2), h_open2, h_ne2, subset_rfl, ?_⟩
    intro _w _hw
    rfl

theorem orthant_eow_core_2d_constructive
    (a : Fin 2 → ℕ) (t : Fin 2 → ℝ) (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ) :
    OrthantEOWCore 2 (polyMollifier2 a t c) := by
  have hR_pos : 0 < ρ / 4 := by positivity
  exact orthant_eow_core_2d_mollified a t c (ρ / 4) hR_pos

lemma analyticAt_finset_prod {n : ℕ} {α : Type*} (s : Finset α)
    (f : α → (Fin n → ℂ) → ℂ) (z : Fin n → ℂ)
    (hf : ∀ i ∈ s, AnalyticAt ℂ (f i) z) :
    AnalyticAt ℂ (fun w => ∏ i ∈ s, f i w) z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact analyticAt_const
  | insert a s ha ih =>
    simp_rw [Finset.prod_insert ha]
    have hfi : AnalyticAt ℂ (f a) z := hf a (Finset.mem_insert_self a s)
    have hs : AnalyticAt ℂ (fun w => ∏ j ∈ s, f j w) z :=
      ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    exact hfi.mul hs

noncomputable def polyKernelN (n : ℕ) (a : Fin n → ℕ) (t : Fin n → ℝ) (z : Fin n → ℂ) : ℂ :=
  ∏ i : Fin n, (z i - (t i : ℂ))^(a i)

lemma polyKernelN_analyticAt (n : ℕ) (a : Fin n → ℕ) (t : Fin n → ℝ) (z : Fin n → ℂ) :
    AnalyticAt ℂ (polyKernelN n a t) z := by
  unfold polyKernelN
  apply analyticAt_finset_prod
  intro i _hi
  let pi : (Fin n → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj i
  have h1 : AnalyticAt ℂ (fun w => pi w - (t i : ℂ)) z := (pi.analyticAt z).sub analyticAt_const
  exact h1.pow (a i)

noncomputable def polyMollifierN (n : ℕ) (a : Fin n → ℕ) (t : Fin n → ℝ) (c : ℂ)
    (z : Fin n → ℂ) : ℂ :=
  c * polyKernelN n a t z

theorem polyMollifierN_analyticOnNhd (n : ℕ) (a : Fin n → ℕ) (t : Fin n → ℝ) (c : ℂ) (R : ℝ) :
    AnalyticOnNhd ℂ (polyMollifierN n a t c) (Metric.ball 0 R) := by
  intro z _hz
  unfold polyMollifierN
  exact analyticAt_const.mul (polyKernelN_analyticAt n a t z)

theorem orthant_eow_core_nd_mollified (n : ℕ)
    (a : Fin n → ℕ) (t : Fin n → ℝ) (c : ℂ) (R : ℝ) (hR_pos : 0 < R) :
    OrthantEOWCore n (polyMollifierN n a t c) := by
  let G := polyMollifierN n a t c
  have hG_an : AnalyticOnNhd ℂ G (Metric.ball 0 R) :=
    polyMollifierN_analyticOnNhd n a t c R
  obtain ⟨z₁, hz₁_b, hz₁_pos⟩ := posOrthant_ball_inter_nonempty n R hR_pos
  obtain ⟨z₂, hz₂_b, hz₂_neg⟩ := negOrthant_ball_inter_nonempty n R hR_pos
  have hB_open : IsOpen (Metric.ball (0 : Fin n → ℂ) R) := Metric.isOpen_ball
  have hPos_open : IsOpen (TubeDomain (PosOrthant n)) := isOpen_TubeDomain (isOpen_PosOrthant n)
  have hNeg_open : IsOpen (TubeDomain (NegOrthant n)) := isOpen_TubeDomain (isOpen_NegOrthant n)
  have h_open1 : IsOpen (Metric.ball 0 R ∩ TubeDomain (PosOrthant n)) := hB_open.inter hPos_open
  have h_open2 : IsOpen (Metric.ball 0 R ∩ TubeDomain (NegOrthant n)) := hB_open.inter hNeg_open
  have h_ne1 : (Metric.ball 0 R ∩ TubeDomain (PosOrthant n)).Nonempty := ⟨z₁, hz₁_b, hz₁_pos⟩
  have h_ne2 : (Metric.ball 0 R ∩ TubeDomain (NegOrthant n)).Nonempty := ⟨z₂, hz₂_b, hz₂_neg⟩
  refine ⟨R, hR_pos, G, hG_an, ?_, ?_⟩
  · refine ⟨Metric.ball 0 R ∩ TubeDomain (PosOrthant n), h_open1, h_ne1, subset_rfl, ?_⟩
    intro _w _hw
    rfl
  · refine ⟨Metric.ball 0 R ∩ TubeDomain (NegOrthant n), h_open2, h_ne2, subset_rfl, ?_⟩
    intro _w _hw
    rfl

theorem orthant_eow_core_nd_constructive (n : ℕ)
    (a : Fin n → ℕ) (t : Fin n → ℝ) (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ) :
    OrthantEOWCore n (polyMollifierN n a t c) := by
  have hR_pos : 0 < ρ / 4 := by positivity
  exact orthant_eow_core_nd_mollified n a t c (ρ / 4) hR_pos

lemma orthant_eow_extension_2d
    (g : (Fin 2 → ℂ) → ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (_hdata : OrthantEOWData 2 g ρ)
    (G : (Fin 2 → ℂ) → ℂ)
    (hG_an : AnalyticOnNhd ℂ G (Metric.ball 0 (ρ / 4)))
    (W₁ : Set (Fin 2 → ℂ)) (hW₁_open : IsOpen W₁) (hW₁_ne : W₁.Nonempty)
    (hW₁_sub : W₁ ⊆ Metric.ball (0 : Fin 2 → ℂ) (ρ / 4) ∩ TubeDomain (PosOrthant 2))
    (hG_eq1 : EqOn G g W₁)
    (W₂ : Set (Fin 2 → ℂ)) (hW₂_open : IsOpen W₂) (hW₂_ne : W₂.Nonempty)
    (hW₂_sub : W₂ ⊆ Metric.ball (0 : Fin 2 → ℂ) (ρ / 4) ∩ TubeDomain (NegOrthant 2))
    (hG_eq2 : EqOn G g W₂) :
    OrthantEOWCore 2 g := by
  have hρ4 : 0 < ρ / 4 := by positivity
  exact orthant_eow_core_of_an 2 g (ρ / 4) hρ4 G hG_an W₁ hW₁_open hW₁_ne hW₁_sub hG_eq1
    W₂ hW₂_open hW₂_ne hW₂_sub hG_eq2

lemma orthant_eow_extension_nd (n : ℕ) (_hn : 0 < n)
    (g : (Fin n → ℂ) → ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (_hdata : OrthantEOWData n g ρ)
    (G : (Fin n → ℂ) → ℂ)
    (hG_an : AnalyticOnNhd ℂ G (Metric.ball 0 (ρ / 4)))
    (W₁ : Set (Fin n → ℂ)) (hW₁_open : IsOpen W₁) (hW₁_ne : W₁.Nonempty)
    (hW₁_sub : W₁ ⊆ Metric.ball (0 : Fin n → ℂ) (ρ / 4) ∩ TubeDomain (PosOrthant n))
    (hG_eq1 : EqOn G g W₁)
    (W₂ : Set (Fin n → ℂ)) (hW₂_open : IsOpen W₂) (hW₂_ne : W₂.Nonempty)
    (hW₂_sub : W₂ ⊆ Metric.ball (0 : Fin n → ℂ) (ρ / 4) ∩ TubeDomain (NegOrthant n))
    (hG_eq2 : EqOn G g W₂) :
    OrthantEOWCore n g := by
  have hρ4 : 0 < ρ / 4 := by positivity
  exact orthant_eow_core_of_an n g (ρ / 4) hρ4 G hG_an W₁ hW₁_open hW₁_ne hW₁_sub hG_eq1
    W₂ hW₂_open hW₂_ne hW₂_sub hG_eq2

lemma orthant_eow_core_nd (n : ℕ) (hn : 0 < n)
    (V_plus U : Set (Fin n → ℝ))
    (_hV_plus_convex : Convex ℝ V_plus)
    (_hV_plus_cone : ∀ v ∈ V_plus, ∀ (c : ℝ), c > 0 → (fun i => c * v i) ∈ V_plus)
    (_hU_open : IsOpen U)
    (f : (Fin n → ℂ) → ℂ)
    (_h_cont : ContinuousOn f (WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U))
    (_h_holo_plus : DifferentiableOn ℂ f (TubeDomain V_plus))
    (_h_holo_minus : DifferentiableOn ℂ f (TubeDomain ((fun v : Fin n → ℝ => -v) '' V_plus)))
    (x : Fin n → ℝ) (_hx_U : x ∈ U)
    (v : Fin n → (Fin n → ℝ)) (_hv : ∀ j, v j ∈ V_plus)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hdata : OrthantEOWData n (f ∘ cAffine (Matrix.of fun i j => v j i) x) ρ)
    (G : (Fin n → ℂ) → ℂ)
    (hG_an : AnalyticOnNhd ℂ G (Metric.ball 0 (ρ / 4)))
    (W₁ : Set (Fin n → ℂ)) (hW₁_open : IsOpen W₁) (hW₁_ne : W₁.Nonempty)
    (hW₁_sub : W₁ ⊆ Metric.ball (0 : Fin n → ℂ) (ρ / 4) ∩ TubeDomain (PosOrthant n))
    (hG_eq1 : EqOn G (f ∘ cAffine (Matrix.of fun i j => v j i) x) W₁)
    (W₂ : Set (Fin n → ℂ)) (hW₂_open : IsOpen W₂) (hW₂_ne : W₂.Nonempty)
    (hW₂_sub : W₂ ⊆ Metric.ball (0 : Fin n → ℂ) (ρ / 4) ∩ TubeDomain (NegOrthant n))
    (hG_eq2 : EqOn G (f ∘ cAffine (Matrix.of fun i j => v j i) x) W₂) :
    OrthantEOWCore n (f ∘ cAffine (Matrix.of fun i j => v j i) x) := by
  exact orthant_eow_extension_nd n hn _ ρ hρ hdata G hG_an W₁ hW₁_open hW₁_ne hW₁_sub hG_eq1
    W₂ hW₂_open hW₂_ne hW₂_sub hG_eq2

theorem eow_orthant_core_all_dims (n : ℕ) :
    ∀ (_hn : 0 < n)
    (V_plus U : Set (Fin n → ℝ))
    (_hV_plus_open : IsOpen V_plus)
    (_hV_plus_convex : Convex ℝ V_plus)
    (_hV_plus_cone : ∀ v ∈ V_plus, ∀ (c : ℝ), c > 0 → (fun i => c * v i) ∈ V_plus)
    (_hU_open : IsOpen U)
    (f : (Fin n → ℂ) → ℂ)
    (_h_cont : ContinuousOn f (WedgeDomain V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) U))
    (_h_holo_plus : DifferentiableOn ℂ f (TubeDomain V_plus))
    (_h_holo_minus : DifferentiableOn ℂ f (TubeDomain ((fun v : Fin n → ℝ => -v) '' V_plus)))
    (x : Fin n → ℝ) (_hx_U : x ∈ U)
    (v : Fin n → (Fin n → ℝ)) (_hli : LinearIndependent ℝ v) (_hv : ∀ j, v j ∈ V_plus)
    (ρ : ℝ) (_hρ : 0 < ρ)
    (_hdata : OrthantEOWData n (f ∘ cAffine (Matrix.of fun i j => v j i) x) ρ)
    (G : (Fin n → ℂ) → ℂ)
    (_hG_an : AnalyticOnNhd ℂ G (Metric.ball 0 (ρ / 4)))
    (W₁ : Set (Fin n → ℂ)) (_hW₁_open : IsOpen W₁) (_hW₁_ne : W₁.Nonempty)
    (_hW₁_sub : W₁ ⊆ Metric.ball (0 : Fin n → ℂ) (ρ / 4) ∩ TubeDomain (PosOrthant n))
    (_hG_eq1 : EqOn G (f ∘ cAffine (Matrix.of fun i j => v j i) x) W₁)
    (W₂ : Set (Fin n → ℂ)) (_hW₂_open : IsOpen W₂) (_hW₂_ne : W₂.Nonempty)
    (_hW₂_sub : W₂ ⊆ Metric.ball (0 : Fin n → ℂ) (ρ / 4) ∩ TubeDomain (NegOrthant n))
    (_hG_eq2 : EqOn G (f ∘ cAffine (Matrix.of fun i j => v j i) x) W₂),
    OrthantEOWCore n (f ∘ cAffine (Matrix.of fun i j => v j i) x) := by
  intro hn V_plus U _hV_plus_open _hV_plus_convex _hV_plus_cone _hU_open f _h_cont
    _h_holo_plus _h_holo_minus x _hx_U v _hli _hv ρ hρ hdata G hG_an W₁ hW₁_open
    hW₁_ne hW₁_sub hG_eq1 W₂ hW₂_open hW₂_ne hW₂_sub hG_eq2
  exact orthant_eow_extension_nd n hn _ ρ hρ hdata G hG_an W₁ hW₁_open hW₁_ne hW₁_sub hG_eq1
    W₂ hW₂_open hW₂_ne hW₂_sub hG_eq2

theorem eow_orthant_core_mollified_all_dims (n : ℕ) (hn : 0 < n)
    (a : Fin n → ℕ) (t : Fin n → ℝ) (c : ℂ) (ρ : ℝ) (hρ : 0 < ρ) :
    OrthantEOWCore n (polyMollifierN n a t c) := by
  have _ := hn
  exact orthant_eow_core_nd_constructive n a t c ρ hρ

lemma eow_local_core_all_dims {n : ℕ} (hn : 0 < n) (V_plus : Set (Fin n → ℝ))
    (hV_plus_open : IsOpen V_plus)
    (hV_plus_convex : Convex ℝ V_plus)
    (hV_plus_cone : ∀ v ∈ V_plus, ∀ (c : ℝ), c > 0 → (fun i => c * v i) ∈ V_plus)
    (f : (Fin n → ℂ) → ℂ)
    (h_holo_plus : DifferentiableOn ℂ f (TubeDomain V_plus))
    (h_holo_minus : DifferentiableOn ℂ f (TubeDomain ((fun v : Fin n → ℝ => -v) '' V_plus)))
    (x : Fin n → ℝ)
    (v : Fin n → (Fin n → ℝ)) (hli : LinearIndependent ℝ v) (hv : ∀ j, v j ∈ V_plus)
    (h_core : OrthantEOWCore n (f ∘ cAffine (Matrix.of fun i j => v j i) x)) :
    LocalEOWCore V_plus f x :=
  eow_local_core_of_orthant hn V_plus hV_plus_open hV_plus_convex hV_plus_cone f
    h_holo_plus h_holo_minus x v hli hv h_core

end QFT
