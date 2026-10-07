import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Topology.Basic
import Mathlib.Order.Filter.Basic

open Complex Filter Topology Set ContinuousLinearMap ContinuousMultilinearMap

namespace Analysis


lemma complex_multilinear_zero_of_real_zero_N {ι : Type*} [Fintype ι] (k : ℕ)
    (p : ContinuousMultilinearMap ℂ (fun _ : Fin k => (ι → ℂ)) ℂ)
    (ofRealN : (ι → ℝ) →L[ℝ] (ι → ℂ))
    (h_ofReal : ∀ x : ι → ℝ, ofRealN x = (fun i => (x i : ℂ)))
    (h : ∀ x : Fin k → (ι → ℝ), p (fun i => ofRealN (x i)) = 0) :
    p = 0 := by
  
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  
  classical
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
  have h_freq_real : Filter.Frequently (fun (t : ℝ) => h (t : ℂ) = 0) (𝓝[≠] a) := h_sub_ne.frequently
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

lemma symm_multilinear_real_eq_zero_of_diagonal_zero_N {ι : Type*} [Fintype ι] {n : ℕ}
    (p : ContinuousMultilinearMap ℝ (fun _ : Fin n => (ι → ℝ)) ℂ)
    (h_symm : ∀ (σ : Equiv.Perm (Fin n)) (v : Fin n → (ι → ℝ)), p (fun i => v (σ i)) = p v)
    (h_diag : ∀ x : (ι → ℝ), p (fun _ => x) = 0) :
    p = 0 := by
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

lemma complex_multilinear_zero_of_diagonal_real_zero_N {ι : Type*} [Fintype ι] {n : ℕ}
    (p : ContinuousMultilinearMap ℂ (fun _ : Fin n => (ι → ℂ)) ℂ)
    (h_symm : ∀ (σ : Equiv.Perm (Fin n)) (v : Fin n → (ι → ℂ)), p (fun i => v (σ i)) = p v)
    (ofRealN : (ι → ℝ) →L[ℝ] (ι → ℂ))
    (h_ofReal : ∀ x : ι → ℝ, ofRealN x = (fun i => (x i : ℂ)))
    (h_diag : ∀ x : (ι → ℝ), p (fun _ => ofRealN x) = 0) :
    p = 0 := by
  let p_real := (p.restrictScalars ℝ).compContinuousLinearMap (fun _ => ofRealN)
  have h_symm_real : ∀ (σ : Equiv.Perm (Fin n)) (v : Fin n → (ι → ℝ)), p_real (fun i => v (σ i)) = p_real v := by
    intro σ v
    exact h_symm σ (fun i => ofRealN (v i))
  have h_diag_real : ∀ x : (ι → ℝ), p_real (fun _ => x) = 0 := h_diag
  have p_real_zero := symm_multilinear_real_eq_zero_of_diagonal_zero_N p_real h_symm_real h_diag_real
  have h_eval : ∀ v : Fin n → (ι → ℝ), p (fun i => ofRealN (v i)) = 0 := by
    intro v
    have h_zero : p_real v = (0 : ContinuousMultilinearMap ℝ (fun _ : Fin n => (ι → ℝ)) ℂ) v := by
      rw [p_real_zero]
    exact h_zero
  exact complex_multilinear_zero_of_real_zero_N n p ofRealN h_ofReal h_eval

lemma ftaylorSeries_isSymmetric {ι : Type*} [Fintype ι] {n : ℕ} (f : (ι → ℂ) → ℂ) (a : ι → ℂ) (hf : AnalyticAt ℂ f a) :
    ∀ (σ : Equiv.Perm (Fin n)) (v : Fin n → (ι → ℂ)),
      (ftaylorSeries ℂ f a) n (fun i => v (σ i)) = (ftaylorSeries ℂ f a) n v := by
  intro σ v
  have h_cont : ContDiffAt ℂ ⊤ f a := hf.contDiffAt
  exact h_cont.iteratedFDeriv_comp_perm v σ

lemma ftaylorSeries_diag_zero {ι : Type*} [Fintype ι] {n : ℕ} (f : (ι → ℂ) → ℂ) (a : ι → ℂ) (hf : AnalyticAt ℂ f a)
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
    exact analytic_nhds_eq_of_real_eq_1D (fun z => f (a + L z)) (fun _ => 0) (0 : ℝ) h_g_ana h_zero_ana h_g_real
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
  have h_sum_const : (∑ σ : Equiv.Perm (Fin n), p n (fun _ : Fin n => ofRealN x)) = (Fintype.card (Equiv.Perm (Fin n))) • p n (fun _ => ofRealN x) := by
    exact Finset.sum_const _
  rw [h_sum_const, h_p_zero] at h_sum
  have h_smul_zero : (Fintype.card (Equiv.Perm (Fin n))) • (0 : ℂ) = 0 := smul_zero _
  rw [h_smul_zero] at h_sum
  exact h_sum

lemma eq_zero_of_ftaylorSeries_zero {ι : Type*} [Fintype ι] (f : (ι → ℂ) → ℂ) (a : ι → ℂ) (hf : AnalyticAt ℂ f a)
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
    have h_eval_zero : (0 : ContinuousMultilinearMap ℂ (fun _ : Fin n => (ι → ℂ)) ℂ) (fun _ => y) = 0 := rfl
    rw [h_eval_zero] at h_sum
    have h_sum_const : (∑ σ : Equiv.Perm (Fin n), p n (fun _ : Fin n => y)) = (Fintype.card (Equiv.Perm (Fin n))) • p n (fun _ => y) := by
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
    have h_diag := ftaylorSeries_diag_zero (n := n) (f - g) (ofRealN a) hfg ofRealN h_ofReal h_real_zero
    
    exact complex_multilinear_zero_of_diagonal_real_zero_N ((ftaylorSeries ℂ (f - g) (ofRealN a)) n) h_symm ofRealN h_ofReal h_diag

  
  have h_zero_nhds := eq_zero_of_ftaylorSeries_zero (f - g) (ofRealN a) hfg hp_zero
  filter_upwards [h_zero_nhds] with z hz
  exact sub_eq_zero.mp hz


lemma analytic_eq_of_real_eq_R_N {ι : Type*} [Fintype ι] {U : Set (ι → ℂ)}
    (hU_open : IsOpen U) (hU_conn : IsConnected U)
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

  have h_eq_zero := hfg.eqOn_zero_of_preconnected_of_eventuallyEq_zero hU_conn.isPreconnected ha h_nhds_zero

  intro z hz
  have hz_zero := h_eq_zero hz
  exact sub_eq_zero.mp hz_zero


end Analysis
