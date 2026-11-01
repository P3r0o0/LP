import WightmanFramework
import AnalyticContinuation

namespace QFT

open Geometry Geometry.MatrixAnalysis
open Complex Topology Filter Set
open scoped Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def vector_bhw_diff (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (E : TubeExtension W) (n : ℕ) (z : Fin n → Fin 4 → ℂ) (α : Fin n → ι)
    (x : Fin 6 → ℂ) : ℂ :=
  let Λ := local_chart x
  let A := sl2c_chart_invFun (local_chart_e x).1
  let B := sl2c_chart_invFun (local_chart_e x).2
  E.H n α (Λ • z) - ∑ β : Fin n → ι, (∏ i, R.σ (A, B) (α i) (β i)) * E.H n β z

attribute [local instance] Matrix.normedAddCommGroup
attribute [local instance] Matrix.normedSpace

lemma finset_sum_analyticAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : Type*} (s : Finset ι) (f : ι → E → ℂ) (x : E)
    (hf : ∀ i ∈ s, AnalyticAt ℂ (f i) x) :
    AnalyticAt ℂ (fun e => ∑ i ∈ s, f i e) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact analyticAt_const
  | insert a s ha ih =>
    have h_eq : (fun e => ∑ i ∈ insert a s, f i e) = fun e => f a e + ∑ i ∈ s, f i e := by
      ext e
      exact Finset.sum_insert ha
    rw [h_eq]
    apply AnalyticAt.add
    · exact hf a (Finset.mem_insert_self a s)
    · apply ih
      intro i hi
      exact hf i (Finset.mem_insert_of_mem hi)

lemma fintype_sum_analyticAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : Type*} [Fintype ι] (f : ι → E → ℂ) (x : E)
    (hf : ∀ i, AnalyticAt ℂ (f i) x) :
    AnalyticAt ℂ (fun e => ∑ i : ι, f i e) x := by
  classical
  exact finset_sum_analyticAt Finset.univ f x (fun i _ => hf i)

lemma fintype_prod_analyticAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : Type*} [Fintype ι] (f : ι → E → ℂ) (x : E)
    (hf : ∀ i, AnalyticAt ℂ (f i) x) :
    AnalyticAt ℂ (fun e => ∏ i : ι, f i e) x := by
  classical
  let s := (Finset.univ : Finset ι)
  have h_prod : AnalyticAt ℂ (fun e => ∏ i ∈ s, f i e) x := by
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.prod_empty]
      exact analyticAt_const
    | insert a s ha ih =>
      have h_eq : (fun e => ∏ i ∈ insert a s, f i e) = fun e => f a e * ∏ i ∈ s, f i e := by
        ext e
        exact Finset.prod_insert ha
      rw [h_eq]
      exact AnalyticAt.mul (hf a) ih
  exact h_prod

lemma mvPolynomial_eval_analyticAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {σ : Type*} (P : MvPolynomial σ ℂ)
    (f : σ → E → ℂ) (x : E) (hf : ∀ i, AnalyticAt ℂ (f i) x) :
    AnalyticAt ℂ (fun e => MvPolynomial.eval (fun i => f i e) P) x := by
  apply MvPolynomial.induction_on P
  · intro c
    simp only [MvPolynomial.eval_C]
    exact analyticAt_const
  · intro p q hp hq
    simp only [map_add]
    exact AnalyticAt.add hp hq
  · intro p n hp
    simp only [map_mul, MvPolynomial.eval_X]
    exact AnalyticAt.mul hp (hf n)

lemma rep_sigma_analytic (R : HolomorphicLorentzRep ι) (α β : ι) :
    AnalyticAt ℂ (fun x : Fin 6 → ℂ =>
      let A := sl2c_chart_invFun (local_chart_e x).1
      let B := sl2c_chart_invFun (local_chart_e x).2
      R.σ (A, B) α β) 0 := by
  rcases R.polynomial α β with ⟨P, hP⟩
  have h_eq : (fun x : Fin 6 → ℂ =>
      let A := sl2c_chart_invFun (local_chart_e x).1
      let B := sl2c_chart_invFun (local_chart_e x).2
      R.σ (A, B) α β) = fun x => MvPolynomial.eval (fun i =>
        Sum.elim (fun a => (sl2c_chart_invFun (local_chart_e x).1).1 a.1 a.2)
          (fun a => (sl2c_chart_invFun (local_chart_e x).2).1 a.1 a.2) i) P := by
    ext x
    exact hP (sl2c_chart_invFun (local_chart_e x).1, sl2c_chart_invFun (local_chart_e x).2)
  rw [h_eq]
  apply mvPolynomial_eval_analyticAt
  intro i
  rcases i with a | a
  · have h1 : AnalyticAt ℂ (fun x => (local_chart_e x).1) 0 :=
      ContinuousLinearMap.analyticAt
        (ContinuousLinearMap.fst ℂ (Fin 3 → ℂ) (Fin 3 → ℂ) ∘L
          local_chart_e.toContinuousLinearMap) 0
    have h2 := sl2c_chart_invFun_analytic
    have h0 : (local_chart_e 0).1 = 0 := by ext i; simp [local_chart_e]
    have hA : AnalyticAt ℂ (fun x => (sl2c_chart_invFun (local_chart_e x).1).1) 0 :=
      AnalyticAt.comp (g := fun a => (sl2c_chart_invFun a).1)
        (f := fun x => (local_chart_e x).1) (h0 ▸ h2) h1
    exact analyticAt_matrix_elem hA a.1 a.2
  · have h1 : AnalyticAt ℂ (fun x => (local_chart_e x).2) 0 :=
      ContinuousLinearMap.analyticAt
        (ContinuousLinearMap.snd ℂ (Fin 3 → ℂ) (Fin 3 → ℂ) ∘L
          local_chart_e.toContinuousLinearMap) 0
    have h2 := sl2c_chart_invFun_analytic
    have h0 : (local_chart_e 0).2 = 0 := by ext i; simp [local_chart_e]
    have hB : AnalyticAt ℂ (fun x => (sl2c_chart_invFun (local_chart_e x).2).1) 0 :=
      AnalyticAt.comp (g := fun a => (sl2c_chart_invFun a).1)
        (f := fun x => (local_chart_e x).2) (h0 ▸ h2) h1
    exact analyticAt_matrix_elem hB a.1 a.2

lemma vector_bhw_diff_analytic (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (E : TubeExtension W) (n : ℕ) (z : Fin n → Fin 4 → ℂ) (hz : z ∈ forward_tube_n n)
    (α : Fin n → ι) :
    AnalyticAt ℂ (vector_bhw_diff R W E n z α) 0 := by
  have h1 : AnalyticAt ℂ (fun x => E.H n α (local_chart x • z)) 0 := by
    have h_an_on := E.analytic n α
    have hU : forward_tube_n n ∈ 𝓝 z := (forward_tube_n_isOpen n).mem_nhds hz
    have h_an_at := h_an_on.analyticAt hU
    exact local_chart_analytic n (E.H n α) z h_an_at
  have h2 : AnalyticAt ℂ (fun x => ∑ β : Fin n → ι,
      (∏ i, R.σ (sl2c_chart_invFun (local_chart_e x).1,
        sl2c_chart_invFun (local_chart_e x).2) (α i) (β i)) * E.H n β z) 0 := by
    apply fintype_sum_analyticAt
    intro β
    apply AnalyticAt.mul
    · apply fintype_prod_analyticAt
      intro i
      exact rep_sigma_analytic R (α i) (β i)
    · exact analyticAt_const
  exact AnalyticAt.sub h1 h2

lemma vector_bhw_diff_eq_zero_on_real (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (E : TubeExtension W) (h_cov : TubeCovariant R E) (n : ℕ) (z : Fin n → Fin 4 → ℂ)
    (hz : z ∈ forward_tube_n n) (α : Fin n → ι) (x : Fin 6 → ℝ)
    (h_tube : local_chart (fun i => (x i : ℂ)) • z ∈ forward_tube_n n) :
    vector_bhw_diff R W E n z α (fun i => (x i : ℂ)) = 0 := by
  dsimp [vector_bhw_diff]
  let x_c := fun i => (x i : ℂ)
  let A := sl2c_chart_invFun (local_chart_e x_c).1
  let B := sl2c_chart_invFun (local_chart_e x_c).2
  have hB : B = sl2c_conj A := by
    have h_B1 : B.1 = Matrix.map A.1 star := local_chart_B_eq_map_conj x
    apply Subtype.ext
    exact h_B1
  have h_cov' := h_cov n A z hz
  have h_Lam : local_chart x_c = spinorPhi (A, B) := by rfl
  have h_Lam' : local_chart x_c = spinorPhi (A, sl2c_conj A) := by rw [h_Lam, hB]
  have h_tube' : spinorPhi (A, sl2c_conj A) • z ∈ forward_tube_n n := by
    rw [← h_Lam']
    exact h_tube
  specialize h_cov' h_tube' α
  rw [h_Lam']
  rw [h_cov']
  have h_eq_sum : ∑ β : Fin n → ι, (∏ i : Fin n, R.rep A (α i) (β i)) * E.H n β z =
      ∑ β : Fin n → ι, (∏ i : Fin n, R.σ (A, B) (α i) (β i)) * E.H n β z := by
    apply Finset.sum_congr rfl
    intro β _
    have h_rep : ∀ i, R.rep A (α i) (β i) = R.σ (A, B) (α i) (β i) := by
      intro i
      have hd : R.rep A (α i) (β i) = R.σ (A, sl2c_conj A) (α i) (β i) := by rfl
      rw [hd, ← hB]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    exact h_rep i
  rw [h_eq_sum]
  exact sub_self _

lemma local_chart_action_continuous (n : ℕ) (z : Fin n → Fin 4 → ℂ) :
    ContinuousAt (fun x : Fin 6 → ℂ => local_chart x • z) 0 := by
  have h_act_an : AnalyticAt ℂ (fun x => (local_chart x) • z) 0 := by
    apply AnalyticAt.pi
    intro i
    apply AnalyticAt.pi
    intro j
    have H2 : (fun x => ((local_chart x) • z) i j) =
        fun x => ∑ k : Fin 4, (local_chart x).1.1 j k * z i k := by
      ext x
      rfl
    rw [H2]
    apply fintype_sum_analyticAt
    intro k
    apply AnalyticAt.mul
    · exact analyticAt_matrix_elem4 local_chart_matrix_analytic j k
    · exact analyticAt_const
  exact h_act_an.continuousAt

lemma vector_bhw_diff_eq_zero_near_zero (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (E : TubeExtension W) (h_cov : TubeCovariant R E) (n : ℕ) (z : Fin n → Fin 4 → ℂ)
    (hz : z ∈ forward_tube_n n) (α : Fin n → ι) :
    ∀ᶠ x in 𝓝 (0 : Fin 6 → ℂ), vector_bhw_diff R W E n z α x = 0 := by
  have hF_analytic : AnalyticAt ℂ (vector_bhw_diff R W E n z α) 0 :=
    vector_bhw_diff_analytic R W E n z hz α
  have hG_analytic : AnalyticAt ℂ (fun _ : Fin 6 → ℂ => (0 : ℂ)) 0 := analyticAt_const
  let my_ofRealN : (Fin 6 → ℝ) →L[ℝ] (Fin 6 → ℂ) :=
    ContinuousLinearMap.pi (fun i =>
      ContinuousLinearMap.comp Complex.ofRealCLM (ContinuousLinearMap.proj i))
  have h_ofReal : ∀ x : Fin 6 → ℝ, my_ofRealN x = (fun i => (x i : ℂ)) := fun _ => rfl
  have h_cont_R :
      ContinuousAt (fun x : Fin 6 → ℝ => local_chart (fun i => (x i : ℂ)) • z) 0 := by
    have h_comp : (fun x : Fin 6 → ℝ => local_chart (fun i => (x i : ℂ)) • z) =
        (fun x => local_chart x • z) ∘ my_ofRealN := rfl
    rw [h_comp]
    apply ContinuousAt.comp
    · exact local_chart_action_continuous n z
    · exact my_ofRealN.continuous.continuousAt
  have h_tube_nhds :
      ∀ᶠ x : Fin 6 → ℝ in 𝓝 0, local_chart (fun i => (x i : ℂ)) • z ∈ forward_tube_n n := by
    have h_open := forward_tube_n_isOpen n
    have hz0 : (fun i => ((0 : Fin 6 → ℝ) i : ℂ)) = 0 := by ext i; simp
    have h0 : local_chart (fun i => ((0 : Fin 6 → ℝ) i : ℂ)) • z = z := by
      rw [hz0]
      have h1 : local_chart 0 = 1 := local_chart_zero
      rw [h1]
      exact one_smul _ z
    have hz_nhds : forward_tube_n n ∈ 𝓝 z := h_open.mem_nhds hz
    have h0' : (fun (x : Fin 6 → ℝ) => local_chart (fun i => (x i : ℂ)) • z) 0 = z := h0
    have hz_nhds' :
        forward_tube_n n ∈
          𝓝 ((fun (x : Fin 6 → ℝ) => local_chart (fun i => (x i : ℂ)) • z) 0) := by
      rw [h0']
      exact hz_nhds
    exact h_cont_R.preimage_mem_nhds hz_nhds'
  have h_real_eq :
      ∀ᶠ x : Fin 6 → ℝ in 𝓝 0, vector_bhw_diff R W E n z α (fun i => (x i : ℂ)) = 0 := by
    apply Filter.Eventually.mono h_tube_nhds
    intro x hx
    exact vector_bhw_diff_eq_zero_on_real R W E h_cov n z hz α x hx
  have h_real_eq2 : ∀ᶠ x : Fin 6 → ℝ in 𝓝 0,
      vector_bhw_diff R W E n z α (my_ofRealN x) = (fun _ => (0 : ℂ)) (my_ofRealN x) := by
    apply Filter.Eventually.mono h_real_eq
    intro x hx
    rw [h_ofReal]
    exact hx
  exact Analysis.analytic_nhds_eq_of_real_eq_N (vector_bhw_diff R W E n z α) (fun _ => 0) 0
    my_ofRealN h_ofReal hF_analytic hG_analytic h_real_eq2

lemma sum_prod_S_eq_H (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (E : TubeExtension W) (h_cov : TubeCovariant R E) (n : ℕ) (z : Fin n → Fin 4 → ℂ)
    (hz : z ∈ forward_tube_n n) (α : Fin n → ι) :
    E.H n α z = ∑ β : Fin n → ι, (∏ i, R.σ (-1, -1) (α i) (β i)) * E.H n β z := by
  have hz_inv : spinorPhi ((-1 : SL2C), sl2c_conj (-1 : SL2C)) • z ∈ forward_tube_n n := by
    have h_conj : sl2c_conj (-1 : SL2C) = -1 := by
      apply Subtype.ext; ext i j; fin_cases i <;> fin_cases j <;> simp [sl2c_conj]
    rw [h_conj]
    have h_spinor : spinorPhi ((-1 : SL2C), (-1 : SL2C)) = 1 := by
      have h := Geometry.PolarDecomposition.spinorPhi_neg_neg (1 : SL2C) (1 : SL2C)
      rw [h]; exact map_one spinorPhi
    rw [h_spinor]
    have e : (1 : SpecialSpecialComplexLorentzGroup) • z = z := one_smul _ z
    rw [e]
    exact hz
  have h_cov_apply := h_cov n (-1) z hz hz_inv α
  have h_conj : sl2c_conj (-1 : SL2C) = -1 := by
    apply Subtype.ext; ext i j; fin_cases i <;> fin_cases j <;> simp [sl2c_conj]
  rw [h_conj] at h_cov_apply
  have h_spinor : spinorPhi ((-1 : SL2C), (-1 : SL2C)) = 1 := by
    have h := Geometry.PolarDecomposition.spinorPhi_neg_neg (1 : SL2C) (1 : SL2C)
    rw [h]; exact map_one spinorPhi
  rw [h_spinor] at h_cov_apply
  have h_one_smul : (1 : SpecialSpecialComplexLorentzGroup) • z = z := one_smul _ _
  rw [h_one_smul] at h_cov_apply
  have h_rep : R.rep (-1) = R.σ (-1, -1) := by
    rw [HolomorphicLorentzRep.rep_apply, h_conj]
  simp_rw [h_rep] at h_cov_apply
  exact h_cov_apply

lemma G_eq_G_neg (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (E : TubeExtension W) (h_cov : TubeCovariant R E) (n : ℕ) (z : Fin n → Fin 4 → ℂ)
    (hz : z ∈ forward_tube_n n) (α : Fin n → ι) (A B : SL2C) :
    ∑ β : Fin n → ι, (∏ i, R.σ (-A, -B) (α i) (β i)) * E.H n β z =
    ∑ β : Fin n → ι, (∏ i, R.σ (A, B) (α i) (β i)) * E.H n β z := by
  have h_neg : ((-A, -B) : SL2C × SL2C) = (A, B) * (-1, -1) := by
    ext1
    · apply Subtype.ext; ext i j; fin_cases i <;> fin_cases j <;> simp
    · apply Subtype.ext; ext i j; fin_cases i <;> fin_cases j <;> simp
  have h_sigma : R.σ (-A, -B) = R.σ (A, B) * R.σ (-1, -1) := by
    rw [h_neg, map_mul]
  have h_prod : ∀ β : Fin n → ι, ∏ i, R.σ (-A, -B) (α i) (β i) =
      ∏ i, ∑ k_i : ι, R.σ (A, B) (α i) k_i * R.σ (-1, -1) k_i (β i) := by
    intro β
    apply Finset.prod_congr rfl
    intro i _
    exact congr_fun (congr_fun h_sigma (α i)) (β i)
  have h_sum_prod : ∀ β : Fin n → ι,
      (∏ i, ∑ k_i : ι, R.σ (A, B) (α i) k_i * R.σ (-1, -1) k_i (β i)) =
      ∑ k : Fin n → ι, ∏ i, (R.σ (A, B) (α i) (k i) * R.σ (-1, -1) (k i) (β i)) := by
    intro β
    exact Finset.prod_univ_sum (fun _ => (Finset.univ : Finset ι))
      (fun i k_i => R.σ (A, B) (α i) k_i * R.σ (-1, -1) k_i (β i))
  calc
    ∑ β, (∏ i, R.σ (-A, -B) (α i) (β i)) * E.H n β z
      = ∑ β, (∑ k : Fin n → ι,
          ∏ i, R.σ (A, B) (α i) (k i) * R.σ (-1, -1) (k i) (β i)) * E.H n β z := by
        apply Finset.sum_congr rfl
        intro β _
        rw [h_prod β, h_sum_prod β]
    _ = ∑ β, ∑ k : Fin n → ι,
        (∏ i, R.σ (A, B) (α i) (k i) * R.σ (-1, -1) (k i) (β i)) * E.H n β z := by
        apply Finset.sum_congr rfl
        intro β _
        exact Finset.sum_mul _ _ _
    _ = ∑ k : Fin n → ι, ∑ β,
        (∏ i, R.σ (A, B) (α i) (k i) * R.σ (-1, -1) (k i) (β i)) * E.H n β z := by
        exact Finset.sum_comm
    _ = ∑ k : Fin n → ι, ∑ β,
        (∏ i, R.σ (A, B) (α i) (k i)) * (∏ i, R.σ (-1, -1) (k i) (β i)) * E.H n β z := by
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro β _
        rw [Finset.prod_mul_distrib]
    _ = ∑ k : Fin n → ι,
        (∏ i, R.σ (A, B) (α i) (k i)) * ∑ β, (∏ i, R.σ (-1, -1) (k i) (β i)) * E.H n β z := by
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro β _
        ring
    _ = ∑ k : Fin n → ι, (∏ i, R.σ (A, B) (α i) (k i)) * E.H n k z := by
        apply Finset.sum_congr rfl
        intro k _
        have h_S := sum_prod_S_eq_H R W E h_cov n z hz k
        rw [← h_S]

lemma spinor_action_eq_self_imp (A B : SL2C) (h : spinorPhi (A, B) = 1)
    (X : Matrix (Fin 2) (Fin 2) ℂ) :
    A.1 * X * B.1ᵀ = X := by
  have h_mat : spinorPhi_matrix A B = 1 := by
    have h1 : spinorPhi_matrix A B = (spinorPhi (A, B)).val.val := rfl
    rw [h1, h]
    rfl
  have h_act : ∀ x, spinor_action A.1 B.1 x = x := by
    intro x
    rw [← spinorPhi_matrix_mulVec, h_mat, Matrix.one_mulVec]
  have h1 := h_act (spinor_to_vec X)
  rw [spinor_action, vec_to_spinor_right_inv] at h1
  have h2 := congrArg vec_to_spinor h1
  rw [vec_to_spinor_right_inv, vec_to_spinor_right_inv] at h2
  exact h2

lemma spinorPhi_eq_one_imp (A B : SL2C) (h : spinorPhi (A, B) = 1) :
    (A, B) = (1, 1) ∨ (A, B) = (-1, -1) := by
  have hX := spinor_action_eq_self_imp A B h
  have hAB : A.1 * B.1ᵀ = 1 := by simpa using hX 1
  have hBA : B.1ᵀ * A.1 = 1 := mul_eq_one_comm.mp hAB
  have hcomm : ∀ X : Matrix (Fin 2) (Fin 2) ℂ, A.1 * X = X * A.1 := by
    intro X
    have := hX X
    calc A.1 * X = (A.1 * X * B.1ᵀ) * A.1 := by
          rw [mul_assoc (A.1 * X), hBA, mul_one]
      _ = X * A.1 := by rw [this]
  have e1 := hcomm !![1, 0; 0, 0]
  have e2 := hcomm !![0, 1; 0, 0]
  have hA := Matrix.eta_fin_two A.1
  have hdet : A.1.det = 1 := A.2
  rw [Matrix.det_fin_two] at hdet
  have hb : A.1 0 1 = 0 := by
    have h := (congrFun (congrFun e1 0) 1).symm
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using h
  have hc : A.1 1 0 = 0 := by
    have h := congrFun (congrFun e1 1) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using h
  have had : A.1 0 0 = A.1 1 1 := by
    have h := congrFun (congrFun e2 0) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using h
  set a := A.1 0 0 with ha
  have haa : a * a = 1 := by
    rw [hb, hc, ← had] at hdet
    simpa using hdet
  have hA' : A.1 = !![a, 0; 0, a] := by
    rw [Matrix.eta_fin_two A.1, hb, hc, ← had]
  have h_aB00 : a * B.1 0 0 = 1 := by
    have h := congrFun (congrFun hAB 0) 0
    rw [hA'] at h
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using h
  have hB00 : B.1 0 0 = a := by
    calc B.1 0 0 = (a * a) * B.1 0 0 := by rw [haa, one_mul]
      _ = a * (a * B.1 0 0) := by ring
      _ = a := by rw [h_aB00, mul_one]
  have h_aB11 : a * B.1 1 1 = 1 := by
    have h := congrFun (congrFun hAB 1) 1
    rw [hA'] at h
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using h
  have hB11 : B.1 1 1 = a := by
    calc B.1 1 1 = (a * a) * B.1 1 1 := by rw [haa, one_mul]
      _ = a * (a * B.1 1 1) := by ring
      _ = a := by rw [h_aB11, mul_one]
  have h_aB01 : a = 0 ∨ B.1 0 1 = 0 := by
    have h := congrFun (congrFun hAB 1) 0
    rw [hA'] at h
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using h
  have hB01 : B.1 0 1 = 0 := by
    rcases h_aB01 with h0 | h0
    · have ha_ne : a ≠ 0 := by intro h0'; rw [h0'] at haa; simp at haa
      exact absurd h0 ha_ne
    · exact h0
  have h_aB10 : a = 0 ∨ B.1 1 0 = 0 := by
    have h := congrFun (congrFun hAB 0) 1
    rw [hA'] at h
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using h
  have hB10 : B.1 1 0 = 0 := by
    rcases h_aB10 with h0 | h0
    · have ha_ne : a ≠ 0 := by intro h0'; rw [h0'] at haa; simp at haa
      exact absurd h0 ha_ne
    · exact h0
  have hB' : B.1 = !![a, 0; 0, a] := by
    rw [Matrix.eta_fin_two B.1, hB00, hB01, hB10, hB11]
  rcases mul_self_eq_one_iff.mp haa with h1 | h1
  · left
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · rw [hA', h1]; ext i j; fin_cases i <;> fin_cases j <;> simp
    · rw [hB', h1]; ext i j; fin_cases i <;> fin_cases j <;> simp
  · right
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · rw [hA', h1]; ext i j; fin_cases i <;> fin_cases j <;> simp
    · rw [hB', h1]; ext i j; fin_cases i <;> fin_cases j <;> simp

noncomputable def Tm (R : HolomorphicLorentzRep ι) (n : ℕ) (g : SL2C × SL2C)
    (α β : Fin n → ι) : ℂ :=
  ∏ i, R.σ g (α i) (β i)

lemma Tm_mul (R : HolomorphicLorentzRep ι) (n : ℕ) (g h : SL2C × SL2C) (α β : Fin n → ι) :
    Tm R n (g * h) α β = ∑ γ : Fin n → ι, Tm R n g α γ * Tm R n h γ β := by
  unfold Tm
  have h1 : ∀ i, R.σ (g * h) (α i) (β i) = ∑ k : ι, R.σ g (α i) k * R.σ h k (β i) := by
    intro i; rw [map_mul, Matrix.mul_apply]
  simp_rw [h1]
  have h2 := Finset.prod_univ_sum (fun _ : Fin n => (Finset.univ : Finset ι))
    (fun i k_i => R.σ g (α i) k_i * R.σ h k_i (β i))
  have h3 : ∏ i, ∑ k_i : ι, R.σ g (α i) k_i * R.σ h k_i (β i)
      = ∑ k : Fin n → ι, ∏ i, (R.σ g (α i) (k i) * R.σ h (k i) (β i)) := h2
  rw [h3]
  apply Finset.sum_congr rfl
  intro γ _
  exact Finset.prod_mul_distrib

lemma Tm_one (R : HolomorphicLorentzRep ι) (n : ℕ) (α β : Fin n → ι) :
    Tm R n 1 α β = if α = β then 1 else 0 := by
  unfold Tm
  rw [map_one]
  by_cases h : α = β
  · subst h; simp
  · rw [if_neg h]
    obtain ⟨i, hi⟩ : ∃ i, α i ≠ β i := by
      by_contra hc
      push Not at hc
      exact h (funext hc)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

lemma Tm_injective (R : HolomorphicLorentzRep ι) (n : ℕ) (g : SL2C × SL2C)
    (v : (Fin n → ι) → ℂ) (h : ∀ α, ∑ β, Tm R n g α β * v β = 0) : ∀ γ, v γ = 0 := by
  intro γ
  have h1 : ∑ α, Tm R n g⁻¹ γ α * (∑ β, Tm R n g α β * v β) = 0 := by
    simp [h]
  have h2 : ∑ α, Tm R n g⁻¹ γ α * (∑ β, Tm R n g α β * v β) = v γ := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    have key : ∀ β, ∑ α, Tm R n g⁻¹ γ α * (Tm R n g α β * v β) =
        (if γ = β then 1 else 0) * v β := by
      intro β
      rw [← Tm_one R n γ β, ← inv_mul_cancel g, Tm_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun α _ => by ring)
    simp_rw [key]
    simp
  rw [← h2]; exact h1

noncomputable def dd (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι) (E : TubeExtension W)
    (n : ℕ) (z : Fin n → Fin 4 → ℂ) (g : SL2C × SL2C) (α : Fin n → ι) : ℂ :=
  E.H n α (spinorPhi g • z) - ∑ β, Tm R n g α β * E.H n β z

lemma dd_mul (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι) (E : TubeExtension W)
    (n : ℕ) (z : Fin n → Fin 4 → ℂ) (h g : SL2C × SL2C) (α : Fin n → ι) :
    dd R W E n z (h * g) α =
      (E.H n α (spinorPhi h • (spinorPhi g • z)) -
        ∑ β, Tm R n h α β * E.H n β (spinorPhi g • z)) +
      ∑ β, Tm R n h α β * dd R W E n z g β := by
  unfold dd
  have e1 : spinorPhi (h * g) • z = spinorPhi h • (spinorPhi g • z) := by
    rw [map_mul]; exact mul_smul _ _ _
  rw [e1]
  have e2 : ∑ γ, Tm R n (h * g) α γ * E.H n γ z =
      ∑ β, Tm R n h α β * ∑ γ, Tm R n g β γ * E.H n γ z := by
    simp_rw [Tm_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intros; apply Finset.sum_congr rfl; intros; ring
  rw [e2]
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  ring

lemma dd_neg (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι) (E : TubeExtension W)
    (h_cov : TubeCovariant R E) (n : ℕ) (z : Fin n → Fin 4 → ℂ) (hz : z ∈ forward_tube_n n)
    (g : SL2C × SL2C) (α : Fin n → ι) :
    dd R W E n z (-g.1, -g.2) α = dd R W E n z g α := by
  obtain ⟨A, B⟩ := g
  unfold dd Tm
  rw [Geometry.PolarDecomposition.spinorPhi_neg_neg A B]
  have := G_eq_G_neg R W E h_cov n z hz α A B
  rw [this]

lemma dd_eq_of_phi_eq (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι) (E : TubeExtension W)
    (h_cov : TubeCovariant R E) (n : ℕ) (z : Fin n → Fin 4 → ℂ) (hz : z ∈ forward_tube_n n)
    (g g' : SL2C × SL2C) (h : spinorPhi g = spinorPhi g') (α : Fin n → ι) :
    dd R W E n z g' α = dd R W E n z g α := by
  have hk : spinorPhi (g⁻¹ * g') = 1 := by
    rw [map_mul, map_inv, h, inv_mul_cancel]
  have hg' : g' = g * (g⁻¹ * g') := by simp
  rcases spinorPhi_eq_one_imp (g⁻¹ * g').1 (g⁻¹ * g').2 hk with h1 | h1
  · have : g⁻¹ * g' = 1 := h1
    rw [this, mul_one] at hg'
    rw [← hg']
  · have h2 : g⁻¹ * g' = (-1, -1) := h1
    rw [h2] at hg'
    have h3 : g' = (-g.1, -g.2) := by
      rw [hg']
      refine Prod.ext ?_ ?_ <;> simp
    rw [h3]
    exact dd_neg R W E h_cov n z hz g α

noncomputable def gcart (x : Fin 6 → ℂ) : SL2C × SL2C :=
  (sl2c_chart_invFun (local_chart_e x).1, sl2c_chart_invFun (local_chart_e x).2)

lemma local_chart_eq (x : Fin 6 → ℂ) : local_chart x = spinorPhi (gcart x) := rfl

lemma local_nbhd (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι) (E : TubeExtension W)
    (h_cov : TubeCovariant R E) (n : ℕ) (z : Fin n → Fin 4 → ℂ) (g1 : SL2C × SL2C)
    (hg1 : spinorPhi g1 • z ∈ forward_tube_n n) :
    ∀ᶠ Λ in 𝓝 (spinorPhi g1), ∃ x : Fin 6 → ℂ, Λ = spinorPhi (gcart x * g1) ∧
      ∀ α, vector_bhw_diff R W E n (spinorPhi g1 • z) α x = 0 := by
  have h_ev : ∀ᶠ x in 𝓝 (0 : Fin 6 → ℂ), ∀ α : Fin n → ι,
      vector_bhw_diff R W E n (spinorPhi g1 • z) α x = 0 :=
    Filter.eventually_all.mpr (fun α => vector_bhw_diff_eq_zero_near_zero R W E h_cov n _ hg1 α)
  obtain ⟨U, hU, hUeq⟩ := eventually_iff_exists_mem.mp h_ev
  have h_img := local_chart_isOpenMap_at_zero U hU
  have h_mult : Tendsto (fun Λ : SpecialSpecialComplexLorentzGroup => Λ * (spinorPhi g1)⁻¹)
      (𝓝 (spinorPhi g1)) (𝓝 1) := by
    have h0 := (continuous_mul_const (spinorPhi g1)⁻¹ : Continuous
      (fun Λ : SpecialSpecialComplexLorentzGroup => Λ * (spinorPhi g1)⁻¹)).tendsto (spinorPhi g1)
    rwa [mul_inv_cancel] at h0
  filter_upwards [h_mult h_img] with Λ hΛ
  obtain ⟨x, hx, hxe⟩ := hΛ
  refine ⟨x, ?_, hUeq x hx⟩
  rw [map_mul, ← local_chart_eq, hxe, inv_mul_cancel_right]

theorem complex_covariance_of_real (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (E : TubeExtension W) (h_cov : TubeCovariant R E) :
    ComplexCovariant R E := by
  intro n A B z hz_tube hz_trans α
  let D := orbit_domain n z
  have hD_conn : IsConnected D := is_connected_orbit_domain n z hz_tube
  have hD_open : IsOpen D := orbit_domain_isOpen n z
  let u : Set SpecialSpecialComplexLorentzGroup :=
    {Λ | Λ ∈ D ∧ ∃ g, spinorPhi g = Λ ∧ ∀ α, dd R W E n z g α = 0}
  let v : Set SpecialSpecialComplexLorentzGroup := D \ u
  have hu_open : IsOpen u := by
    rw [isOpen_iff_mem_nhds]
    rintro Λ0 ⟨hΛ0D, g0, hg0, hd0⟩
    subst hg0
    have hz0 : spinorPhi g0 • z ∈ forward_tube_n n := hΛ0D
    have h_loc := local_nbhd R W E h_cov n z g0 hz0
    have h_D : D ∈ 𝓝 (spinorPhi g0) := hD_open.mem_nhds hΛ0D
    filter_upwards [h_loc, h_D] with Λ ⟨x, hΛx, hx0⟩ hD
    refine ⟨hD, gcart x * g0, hΛx.symm, ?_⟩
    intro α'
    rw [dd_mul]
    have h1 : E.H n α' (spinorPhi (gcart x) • (spinorPhi g0 • z)) -
        ∑ β, Tm R n (gcart x) α' β * E.H n β (spinorPhi g0 • z) =
        vector_bhw_diff R W E n (spinorPhi g0 • z) α' x := rfl
    rw [h1, hx0 α']
    simp [hd0]
  have hv_open : IsOpen v := by
    rw [isOpen_iff_mem_nhds]
    rintro Λ1 ⟨hΛ1D, hΛ1u⟩
    obtain ⟨g1, hg1⟩ := spinorPhi_surjective Λ1
    subst hg1
    have hz1 : spinorPhi g1 • z ∈ forward_tube_n n := hΛ1D
    have h_loc := local_nbhd R W E h_cov n z g1 hz1
    have h_D : D ∈ 𝓝 (spinorPhi g1) := hD_open.mem_nhds hΛ1D
    filter_upwards [h_loc, h_D] with Λ ⟨x, hΛx, hx0⟩ hD
    refine ⟨hD, ?_⟩
    rintro ⟨_, g', hg', hd'⟩
    apply hΛ1u
    refine ⟨hΛ1D, g1, rfl, ?_⟩
    have hphi : spinorPhi (gcart x * g1) = spinorPhi g' := by rw [← hΛx, hg']
    have hzero : ∀ α', dd R W E n z (gcart x * g1) α' = 0 := by
      intro α'
      rw [dd_eq_of_phi_eq R W E h_cov n z hz_tube _ _ hphi.symm α']
      exact hd' α'
    have hzero' : ∀ α', ∑ β, Tm R n (gcart x) α' β * dd R W E n z g1 β = 0 := by
      intro α'
      have := hzero α'
      rw [dd_mul] at this
      have h1 : E.H n α' (spinorPhi (gcart x) • (spinorPhi g1 • z)) -
          ∑ β, Tm R n (gcart x) α' β * E.H n β (spinorPhi g1 • z) =
          vector_bhw_diff R W E n (spinorPhi g1 • z) α' x := rfl
      rw [h1, hx0 α', zero_add] at this
      exact this
    exact Tm_injective R n (gcart x) _ hzero'
  have huv : Disjoint u v := by
    rw [Set.disjoint_iff]
    rintro Λ ⟨hu, hv⟩
    exact hv.2 hu
  have h_union : D ⊆ u ∪ v := by
    intro Λ hΛ
    by_cases h : Λ ∈ u
    · exact Or.inl h
    · exact Or.inr ⟨hΛ, h⟩
  have h_nonempty : (D ∩ u).Nonempty := by
    have h1 : (1 : SpecialSpecialComplexLorentzGroup) ∈ D := by
      change (1 : SpecialSpecialComplexLorentzGroup) • z ∈ forward_tube_n n
      have e : (1 : SpecialSpecialComplexLorentzGroup) • z = z := one_smul _ z
      rw [e]; exact hz_tube
    refine ⟨1, h1, h1, 1, map_one _, ?_⟩
    intro α'
    unfold dd
    have e : (1 : SpecialSpecialComplexLorentzGroup) • z = z := one_smul _ z
    rw [map_one, e]
    simp [Tm_one]
  have h_sub : D ⊆ u :=
    hD_conn.isPreconnected.subset_left_of_subset_union hu_open hv_open huv h_union h_nonempty
  have hmem : spinorPhi (A, B) ∈ u := h_sub hz_trans
  obtain ⟨_, g, hg, hd⟩ := hmem
  have := dd_eq_of_phi_eq R W E h_cov n z hz_tube g (A, B) hg α
  rw [hd α] at this
  unfold dd Tm at this
  exact sub_eq_zero.mp this

noncomputable def spinorPT : SpecialSpecialComplexLorentzGroup :=
  spinorPhi (-1, 1)

lemma spinorPT_val_unit :
    spinorPT.val = -(1 : Matrix.GeneralLinearGroup (Fin 4) ℂ) := by
  dsimp [spinorPT]
  have h := Geometry.PolarDecomposition.spinorPhi_neg_left (1 : SL2C) (1 : SL2C)
  have h1 : spinorPhi ((1 : SL2C), (1 : SL2C)) = 1 := map_one spinorPhi
  rw [h1] at h
  exact h

lemma spinorPT_val :
    spinorPT.val.val = -(1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  have h := congrArg Units.val spinorPT_val_unit
  exact h

lemma spinorPhi_one_neg_one :
    spinorPhi ((1 : SL2C), (-1 : SL2C)) = spinorPT := by
  dsimp [spinorPT]
  have h := Geometry.PolarDecomposition.spinorPhi_neg_neg (-1 : SL2C) (1 : SL2C)
  rw [neg_neg] at h
  exact h

lemma spinorPT_smul_vec (v : Fin 4 → ℂ) :
    spinorPT • v = -v := by
  change (spinorPT.val.val).mulVec v = -v
  rw [spinorPT_val, Matrix.neg_mulVec, Matrix.one_mulVec]

lemma spinorPT_smul (n : ℕ) (z : Fin n → Fin 4 → ℂ) :
    spinorPT • z = -z := by
  ext i k
  exact congrFun (spinorPT_smul_vec (z i)) k

lemma spinorPhi_neg_one_one_smul (n : ℕ) (z : Fin n → Fin 4 → ℂ) :
    spinorPhi ((-1 : SL2C), (1 : SL2C)) • z = -z :=
  spinorPT_smul n z

lemma spinorPhi_one_neg_one_smul (n : ℕ) (z : Fin n → Fin 4 → ℂ) :
    spinorPhi ((1 : SL2C), (-1 : SL2C)) • z = -z := by
  rw [spinorPhi_one_neg_one]
  exact spinorPT_smul n z

lemma spinorPT_mul_self :
    spinorPT * spinorPT = 1 := by
  dsimp [spinorPT]
  rw [← map_mul]
  have h : ((-1 : SL2C), (1 : SL2C)) * ((-1 : SL2C), (1 : SL2C)) = 1 := by
    ext1 <;> simp
  rw [h, map_one]

lemma spinorPT_inv :
    spinorPT⁻¹ = spinorPT :=
  inv_eq_of_mul_eq_one_right spinorPT_mul_self

lemma neg_mem_forward_light_cone_iff (v : Fin 4 → ℝ) :
    -v ∈ forward_light_cone ↔ v ∈ backward_light_cone := by
  dsimp [forward_light_cone, backward_light_cone]
  rw [minkowskiInner_explicit, minkowskiInner_explicit]
  simp only [Pi.neg_apply, neg_mul_neg]
  constructor <;> rintro ⟨h0, h1⟩ <;> refine ⟨by linarith, h1⟩

lemma neg_mem_backward_light_cone_iff (v : Fin 4 → ℝ) :
    -v ∈ backward_light_cone ↔ v ∈ forward_light_cone := by
  rw [← neg_mem_forward_light_cone_iff, neg_neg]

lemma neg_diff_im_eq (n : ℕ) (z : Fin n → Fin 4 → ℂ) (i : Fin n) (hi : i.val + 1 < n) :
    (fun k => -(((-z) i - (-z) ⟨i.val + 1, hi⟩) k).im) =
      -(fun k => -((z i - z ⟨i.val + 1, hi⟩) k).im) := by
  ext k
  simp only [Pi.neg_apply, Pi.sub_apply, Complex.sub_im, Complex.neg_im]
  ring

lemma neg_mem_forward_tube_n_iff (n : ℕ) (z : Fin n → Fin 4 → ℂ) :
    -z ∈ forward_tube_n n ↔ z ∈ backward_tube_n n := by
  constructor
  · intro hz i hi
    have h := hz i hi
    rw [neg_diff_im_eq, neg_mem_forward_light_cone_iff] at h
    exact h
  · intro hz i hi
    have h := hz i hi
    rw [← neg_mem_forward_light_cone_iff, ← neg_diff_im_eq] at h
    exact h

lemma neg_rev_diff_eq (n : ℕ) (z : Fin n → Fin 4 → ℂ)
    (i : Fin n) (hi : i.val + 1 < n) :
    ((-(z ∘ Fin.rev)) i - (-(z ∘ Fin.rev)) ⟨i.val + 1, hi⟩) =
      z ⟨n - 1 - (i.val + 1), by omega⟩ -
      z ⟨(n - 1 - (i.val + 1)) + 1, by omega⟩ := by
  ext k
  simp only [Pi.neg_apply, Pi.sub_apply, Function.comp_apply]
  have h1 : (Fin.rev ⟨i.val + 1, hi⟩ : Fin n) = ⟨n - 1 - (i.val + 1), by omega⟩ := by
    ext
    dsimp [Fin.rev]
    omega
  have h2 : (Fin.rev i : Fin n) = ⟨(n - 1 - (i.val + 1)) + 1, by omega⟩ := by
    ext
    dsimp [Fin.rev]
    omega
  rw [h1, h2]
  ring

lemma neg_rev_mem_forward_tube_n (n : ℕ) (z : Fin n → Fin 4 → ℂ)
    (hz : z ∈ forward_tube_n n) :
    -(z ∘ Fin.rev) ∈ forward_tube_n n := by
  intro i hi
  rw [neg_rev_diff_eq n z i hi]
  exact hz ⟨n - 1 - (i.val + 1), by omega⟩ (by dsimp; omega)

lemma neg_rev_involutive (n : ℕ) (z : Fin n → Fin 4 → ℂ) :
    -((-(z ∘ Fin.rev)) ∘ Fin.rev) = z := by
  ext i k
  simp [Fin.rev_rev]

lemma neg_rev_mem_forward_tube_n_iff (n : ℕ) (z : Fin n → Fin 4 → ℂ) :
    -(z ∘ Fin.rev) ∈ forward_tube_n n ↔ z ∈ forward_tube_n n := by
  constructor
  · intro h
    have h2 := neg_rev_mem_forward_tube_n n (-(z ∘ Fin.rev)) h
    rwa [neg_rev_involutive] at h2
  · exact neg_rev_mem_forward_tube_n n z

lemma rev_mem_backward_tube_n (n : ℕ) (z : Fin n → Fin 4 → ℂ)
    (hz : z ∈ forward_tube_n n) :
    (z ∘ Fin.rev) ∈ backward_tube_n n :=
  (neg_mem_forward_tube_n_iff n (z ∘ Fin.rev)).mp (neg_rev_mem_forward_tube_n n z hz)

lemma spinorPT_smul_rev_mem_forward_tube_n (n : ℕ) (z : Fin n → Fin 4 → ℂ)
    (hz : z ∈ forward_tube_n n) :
    spinorPT • (z ∘ Fin.rev) ∈ forward_tube_n n := by
  rw [spinorPT_smul]
  exact neg_rev_mem_forward_tube_n n z hz

lemma backward_tube_subset_extended_tube_n (n : ℕ) :
    backward_tube_n n ⊆ extended_tube_n n := by
  intro z hz
  have h_neg : -z ∈ forward_tube_n n := (neg_mem_forward_tube_n_iff n z).mpr hz
  dsimp [extended_tube_n]
  rw [Set.mem_iUnion]
  refine ⟨spinorPT, -z, h_neg, ?_⟩
  dsimp
  rw [spinorPT_smul, neg_neg]

lemma rev_mem_extended_tube_n (n : ℕ) (z : Fin n → Fin 4 → ℂ)
    (hz : z ∈ forward_tube_n n) :
    (z ∘ Fin.rev) ∈ extended_tube_n n :=
  backward_tube_subset_extended_tube_n n (rev_mem_backward_tube_n n z hz)

theorem vladimirov_complexCovariant (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (hspec : SpectrumCondition W) (hP : PoincareCovariant R W) :
    ComplexCovariant R (vladimirovTubeExtension R W hspec hP) :=
  complex_covariance_of_real R W
    (vladimirovTubeExtension R W hspec hP)
    (vladimirov_tubeCovariant R W hspec hP)

lemma complexCovariant_neg_one_one {W : WightmanFamily ι} (R : HolomorphicLorentzRep ι)
    (E : TubeExtension W) (h_ccov : ComplexCovariant R E)
    (n : ℕ) (z : Fin n → Fin 4 → ℂ)
    (hz : z ∈ forward_tube_n n) (h_neg_z : -z ∈ forward_tube_n n) (α : Fin n → ι) :
    E.H n α (-z) = ∑ β : Fin n → ι, (∏ i, R.σ (-1, 1) (α i) (β i)) * E.H n β z := by
  have h_smul : spinorPhi ((-1 : SL2C), (1 : SL2C)) • z = -z :=
    spinorPhi_neg_one_one_smul n z
  have hz_trans : spinorPhi ((-1 : SL2C), (1 : SL2C)) • z ∈ forward_tube_n n := by
    rwa [h_smul]
  have h_cov := h_ccov n (-1) 1 z hz hz_trans α
  rwa [h_smul] at h_cov

lemma complexCovariant_neg_rev {W : WightmanFamily ι} (R : HolomorphicLorentzRep ι)
    (E : TubeExtension W) (h_ccov : ComplexCovariant R E)
    (n : ℕ) (z : Fin n → Fin 4 → ℂ)
    (hz : z ∈ forward_tube_n n) (hz_rev : (z ∘ Fin.rev) ∈ forward_tube_n n) (α : Fin n → ι) :
    E.H n α (-(z ∘ Fin.rev)) =
      ∑ β : Fin n → ι, (∏ i, R.σ (-1, 1) (α i) (β i)) * E.H n β (z ∘ Fin.rev) :=
  complexCovariant_neg_one_one R E h_ccov n (z ∘ Fin.rev)
    hz_rev (neg_rev_mem_forward_tube_n n z hz) α

lemma prod_spinParity (R : HolomorphicLorentzRep ι) (ε : ℂ)
    (hε : R.HasSpinParity ε) (n : ℕ) (α β : Fin n → ι) :
    (∏ i : Fin n, R.σ (-1, -1) (α i) (β i)) = if α = β then ε ^ n else 0 := by
  rw [hε.1]
  by_cases h : α = β
  · subst h
    simp only [↓reduceIte, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  · rw [if_neg h]
    obtain ⟨i, hi⟩ : ∃ i, α i ≠ β i := by
      by_contra hc
      push Not at hc
      exact h (funext hc)
    exact Finset.prod_eq_zero (Finset.mem_univ i)
      (by simp [Matrix.one_apply_ne hi])

theorem tube_spin_parity_selection (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (E : TubeExtension W) (h_cov : TubeCovariant R E)
    (ε : ℂ) (hε : R.HasSpinParity ε)
    (n : ℕ) (z : Fin n → Fin 4 → ℂ) (hz : z ∈ forward_tube_n n) (α : Fin n → ι) :
    E.H n α z = ε ^ n * E.H n α z := by
  have h_sum := sum_prod_S_eq_H R W E h_cov n z hz α
  simp_rw [prod_spinParity R ε hε n α] at h_sum
  simpa using h_sum

theorem tube_eq_zero_of_odd_fermion (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (E : TubeExtension W) (h_cov : TubeCovariant R E)
    (hε : R.HasSpinParity (-1))
    (n : ℕ) (hn : Odd n) (z : Fin n → Fin 4 → ℂ) (hz : z ∈ forward_tube_n n) (α : Fin n → ι) :
    E.H n α z = 0 := by
  have h_sel := tube_spin_parity_selection R W E h_cov (-1) hε n z hz α
  rw [Odd.neg_one_pow hn] at h_sel
  linear_combination (1 / 2 : ℂ) * h_sel

open MeasureTheory

noncomputable def tubeBasePoint (n : ℕ) : Fin n → Fin 4 → ℂ :=
  fun i k => Complex.I * (((i.val : ℝ) * unit_time_vector k : ℝ) : ℂ)

lemma tubeBasePoint_mem_forward_tube_n (n : ℕ) :
    tubeBasePoint n ∈ forward_tube_n n := by
  intro i hi
  have h_eq : (fun k => -((tubeBasePoint n i - tubeBasePoint n ⟨i.val + 1, hi⟩) k).im) =
      unit_time_vector := by
    ext k
    simp only [tubeBasePoint, Pi.sub_apply, Complex.sub_im, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, one_mul, Nat.cast_add, Nat.cast_one]
    ring
  rw [h_eq]
  exact unit_time_vector_mem_forward_light_cone

def spacelikeVec : Fin 4 → ℝ :=
  fun k => if k = 1 then -1 else 0

lemma is_spacelike_of_mem_ball_spacelikeVec (u : Fin 4 → ℝ)
    (hu : u ∈ Metric.ball spacelikeVec (1 / 2)) :
    is_spacelike u := by
  rw [Metric.mem_ball, dist_eq_norm] at hu
  have h0 : ‖(u - spacelikeVec) 0‖ < 1 / 2 :=
    lt_of_le_of_lt (norm_le_pi_norm (u - spacelikeVec) 0) hu
  have h1 : ‖(u - spacelikeVec) 1‖ < 1 / 2 :=
    lt_of_le_of_lt (norm_le_pi_norm (u - spacelikeVec) 1) hu
  have h0_eq : (u - spacelikeVec) 0 = u 0 := by
    dsimp [spacelikeVec]; ring
  have h1_eq : (u - spacelikeVec) 1 = u 1 + 1 := by
    dsimp [spacelikeVec]; ring
  rw [h0_eq, Real.norm_eq_abs, abs_lt] at h0
  rw [h1_eq, Real.norm_eq_abs, abs_lt] at h1
  have h2_sq : 0 ≤ u 2 * u 2 := mul_self_nonneg (u 2)
  have h3_sq : 0 ≤ u 3 * u 3 := mul_self_nonneg (u 3)
  dsimp [is_spacelike]
  rw [minkowskiInner_explicit]
  nlinarith

def jostCenter (n : ℕ) : Fin n → Fin 4 → ℝ :=
  fun i k => if k = 1 then (i.val : ℝ) else 0

lemma jostCenter_diff (n : ℕ) (i : Fin n) (hi : i.val + 1 < n) :
    jostCenter n i - jostCenter n ⟨i.val + 1, hi⟩ = spacelikeVec := by
  ext k
  dsimp [jostCenter, spacelikeVec]
  split_ifs <;> push_cast <;> ring

lemma ball_jostCenter_subset_jost_points_n (n : ℕ) :
    Metric.ball (jostCenter n) (1 / 4) ⊆ jost_points_n n := by
  intro x hx
  rw [Metric.mem_ball, dist_eq_norm] at hx
  have h_diff : jost_differences_n n x ⊆ Metric.ball spacelikeVec (1 / 2) := by
    rintro v ⟨i, hi, rfl⟩
    let j : Fin n := ⟨i.val + 1, hi⟩
    rw [Metric.mem_ball, dist_eq_norm]
    have h_sub : x i - x j - spacelikeVec =
        (x - jostCenter n) i - (x - jostCenter n) j := by
      rw [← jostCenter_diff n i hi]
      ext k
      simp only [Pi.sub_apply]
      ring
    rw [h_sub]
    have hi_norm : ‖(x - jostCenter n) i‖ ≤ ‖x - jostCenter n‖ :=
      norm_le_pi_norm (x - jostCenter n) i
    have hj_norm : ‖(x - jostCenter n) j‖ ≤ ‖x - jostCenter n‖ :=
      norm_le_pi_norm (x - jostCenter n) j
    have h_tri : ‖(x - jostCenter n) i - (x - jostCenter n) j‖ ≤
        ‖(x - jostCenter n) i‖ + ‖(x - jostCenter n) j‖ :=
      norm_sub_le _ _
    linarith
  have h_hull : jost_convex_hull n x ⊆ Metric.ball spacelikeVec (1 / 2) :=
    convexHull_min h_diff (convex_ball spacelikeVec (1 / 2))
  intro v hv
  exact is_spacelike_of_mem_ball_spacelikeVec v (h_hull hv)

noncomputable def jostBump (n : ℕ) : ContDiffBump (jostCenter n) where
  rIn := 1 / 8
  rOut := 1 / 4
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

lemma jostBump_complex_hasCompactSupport (n : ℕ) :
    HasCompactSupport (fun x : Fin n → Fin 4 → ℝ => ((jostBump n x : ℝ) : ℂ)) :=
  (jostBump n).hasCompactSupport.comp_left Complex.ofReal_zero

lemma jostBump_complex_contDiff (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin n → Fin 4 → ℝ => ((jostBump n x : ℝ) : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (jostBump n).contDiff

noncomputable def jostSchwartz (n : ℕ) : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ :=
  (jostBump_complex_hasCompactSupport n).toSchwartzMap (jostBump_complex_contDiff n)

lemma jostSchwartz_apply (n : ℕ) (x : Fin n → Fin 4 → ℝ) :
    jostSchwartz n x = ((jostBump n x : ℝ) : ℂ) := rfl

lemma jostSchwartz_mem_jost_points_of_ne_zero (n : ℕ) (x : Fin n → Fin 4 → ℝ)
    (hx : jostSchwartz n x ≠ 0) :
    x ∈ jost_points_n n := by
  have hx_bump : jostBump n x ≠ 0 := by
    intro h0
    apply hx
    rw [jostSchwartz_apply, h0, Complex.ofReal_zero]
  have hx_supp : x ∈ Function.support (jostBump n) := hx_bump
  rw [(jostBump n).support_eq] at hx_supp
  exact ball_jostCenter_subset_jost_points_n n hx_supp

lemma integral_jostSchwartz_ne_zero (n : ℕ) :
    (∫ x : Fin n → Fin 4 → ℝ, jostSchwartz n x) ≠ 0 := by
  have h_re : (∫ x : Fin n → Fin 4 → ℝ, ((jostBump n x : ℝ) : ℂ)) =
      Complex.ofReal (∫ x : Fin n → Fin 4 → ℝ, (jostBump n x : ℝ)) :=
    integral_ofReal
  intro h0
  change (∫ x : Fin n → Fin 4 → ℝ, ((jostBump n x : ℝ) : ℂ)) = 0 at h0
  rw [h_re, Complex.ofReal_eq_zero] at h0
  exact ne_of_gt (ContDiffBump.integral_pos (jostBump n)) h0

lemma abs_det_of_involutive_cle (n : ℕ)
    (e : (Fin n → Fin 4 → ℝ) ≃L[ℝ] (Fin n → Fin 4 → ℝ))
    (h_inv : ∀ x, e (e x) = x) :
    |LinearMap.det e.toLinearMap| = 1 := by
  have h_comp : e.toLinearMap.comp e.toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    intro x
    exact h_inv x
  have h_det := congr_arg LinearMap.det h_comp
  rw [LinearMap.det_comp, LinearMap.det_id] at h_det
  rcases mul_self_eq_one_iff.mp h_det with h | h
  · rw [h, abs_one]
  · rw [h, abs_neg, abs_one]

lemma measurePreserving_of_involutive_cle (n : ℕ)
    (e : (Fin n → Fin 4 → ℝ) ≃L[ℝ] (Fin n → Fin 4 → ℝ))
    (h_inv : ∀ x, e (e x) = x) :
    MeasurePreserving e volume volume := by
  have h_abs := abs_det_of_involutive_cle n e h_inv
  have h_det_ne : LinearMap.det e.toLinearMap ≠ 0 := by
    intro hz
    rw [hz, abs_zero] at h_abs
    exact zero_ne_one h_abs
  have h_map := Measure.map_linearMap_addHaar_eq_smul_addHaar volume h_det_ne
  rw [abs_inv, h_abs, inv_one, ENNReal.ofReal_one, one_smul] at h_map
  exact ⟨e.continuous.measurable, h_map⟩

lemma integral_comp_of_involutive_cle (n : ℕ)
    (e : (Fin n → Fin 4 → ℝ) ≃L[ℝ] (Fin n → Fin 4 → ℝ))
    (h_inv : ∀ x, e (e x) = x)
    (g : (Fin n → Fin 4 → ℝ) → ℂ) :
    (∫ x, g (e x)) = ∫ x, g x := by
  have h_meas := measurePreserving_of_involutive_cle n e h_inv
  have h_emb : MeasurableEmbedding e := e.toHomeomorph.isClosedEmbedding.measurableEmbedding
  exact h_meas.integral_comp h_emb g

def revLinearEquiv (n : ℕ) : (Fin n → Fin 4 → ℝ) ≃ₗ[ℝ] (Fin n → Fin 4 → ℝ) where
  toFun x i := x (Fin.rev i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun x i := x (Fin.rev i)
  left_inv x := by ext i k; simp [Fin.rev_rev]
  right_inv x := by ext i k; simp [Fin.rev_rev]

noncomputable def revCLE (n : ℕ) : (Fin n → Fin 4 → ℝ) ≃L[ℝ] (Fin n → Fin 4 → ℝ) :=
  (revLinearEquiv n).toContinuousLinearEquiv

lemma revCLE_apply (n : ℕ) (x : Fin n → Fin 4 → ℝ) :
    revCLE n x = fun i => x (Fin.rev i) := rfl

lemma revCLE_involutive (n : ℕ) (x : Fin n → Fin 4 → ℝ) :
    revCLE n (revCLE n x) = x := by
  ext i k
  simp [revCLE_apply, Fin.rev_rev]

lemma integral_comp_rev (n : ℕ) (g : (Fin n → Fin 4 → ℝ) → ℂ) :
    (∫ x : Fin n → Fin 4 → ℝ, g (fun i => x (Fin.rev i))) = ∫ x, g x :=
  integral_comp_of_involutive_cle n (revCLE n) (revCLE_involutive n) g

noncomputable def schwartzRevCLM (n : ℕ) :
    SchwartzMap (Fin n → Fin 4 → ℝ) ℂ →L[ℂ] SchwartzMap (Fin n → Fin 4 → ℝ) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (revCLE n)

@[simp]
lemma schwartzRevCLM_apply (n : ℕ) (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    (x : Fin n → Fin 4 → ℝ) :
    schwartzRevCLM n f x = f (fun i => x (Fin.rev i)) := rfl

def pctLinearEquiv (n : ℕ) : (Fin n → Fin 4 → ℝ) ≃ₗ[ℝ] (Fin n → Fin 4 → ℝ) where
  toFun x i := -x (Fin.rev i)
  map_add' x y := by ext i k; simp [add_comm]
  map_smul' c x := by ext i k; simp
  invFun x i := -x (Fin.rev i)
  left_inv x := by ext i k; simp [Fin.rev_rev]
  right_inv x := by ext i k; simp [Fin.rev_rev]

noncomputable def pctCLE (n : ℕ) : (Fin n → Fin 4 → ℝ) ≃L[ℝ] (Fin n → Fin 4 → ℝ) :=
  (pctLinearEquiv n).toContinuousLinearEquiv

lemma pctCLE_apply (n : ℕ) (x : Fin n → Fin 4 → ℝ) :
    pctCLE n x = fun i => -x (Fin.rev i) := rfl

lemma pctCLE_involutive (n : ℕ) (x : Fin n → Fin 4 → ℝ) :
    pctCLE n (pctCLE n x) = x := by
  ext i k
  simp [pctCLE_apply, Fin.rev_rev]

lemma integral_comp_pct (n : ℕ) (g : (Fin n → Fin 4 → ℝ) → ℂ) :
    (∫ x : Fin n → Fin 4 → ℝ, g (fun i => -x (Fin.rev i))) = ∫ x, g x :=
  integral_comp_of_involutive_cle n (pctCLE n) (pctCLE_involutive n) g

noncomputable def schwartzPCTCLM (n : ℕ) :
    SchwartzMap (Fin n → Fin 4 → ℝ) ℂ →L[ℂ] SchwartzMap (Fin n → Fin 4 → ℝ) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (pctCLE n)

@[simp]
lemma schwartzPCTCLM_apply (n : ℕ) (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    (x : Fin n → Fin 4 → ℝ) :
    schwartzPCTCLM n f x = f (fun i => -x (Fin.rev i)) := rfl

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_H_eq_zero_eval {W : WightmanFamily ι} (hspec : SpectrumCondition W)
    (n : ℕ) (α : Fin n → ι) (z : Fin n → Fin 4 → ℂ) :
    vladimirov_H W n α z = vladimirov_H W n α 0 :=
  vladimirov_H_eq_const_of_zero_fourier W n α (fun g hg => hspec n α g (Or.inr hg)) z

omit [Fintype ι] [DecidableEq ι] in
lemma W_n_eq_vladimirov_H_zero_mul_integral {W : WightmanFamily ι} (hspec : SpectrumCondition W)
    (n : ℕ) (α : Fin n → ι) (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    W n α f = vladimirov_H W n α 0 * ∫ x, f x :=
  W_n_eq_integral_of_zero_fourier W n α (fun g hg => hspec n α g (Or.inr hg)) f

def TubeWeakLocality (η : ℂ) {W : WightmanFamily ι} (E : TubeExtension W) : Prop :=
  ∀ (n : ℕ) (α : Fin n → ι) (z : Fin n → Fin 4 → ℂ),
    z ∈ forward_tube_n n →
    E.H n α (-(z ∘ Fin.rev)) = η ^ (n * (n - 1) / 2) * E.H n (α ∘ Fin.rev) z

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_H_zero_weakLocality {W : WightmanFamily ι} {η : ℂ}
    (hspec : SpectrumCondition W) (hloc : WeakLocality η W)
    (n : ℕ) (α : Fin n → ι) :
    vladimirov_H W n α 0 = η ^ (n * (n - 1) / 2) * vladimirov_H W n (α ∘ Fin.rev) 0 := by
  let f := jostSchwartz n
  let f' := schwartzRevCLM n f
  have hf_jost : ∀ x, f x ≠ 0 → x ∈ jost_points_n n :=
    jostSchwartz_mem_jost_points_of_ne_zero n
  have hf'_rev : ∀ x : Fin n → Fin 4 → ℝ, f' (fun i => x (Fin.rev i)) = f x := by
    intro x
    dsimp [f']
    congr 1
    ext i k
    simp [Fin.rev_rev]
  have hW := hloc n α f f' hf_jost hf'_rev
  rw [W_n_eq_vladimirov_H_zero_mul_integral hspec n α f,
      W_n_eq_vladimirov_H_zero_mul_integral hspec n (α ∘ Fin.rev) f'] at hW
  have h_int_eq : (∫ x, f' x) = ∫ x, f x :=
    integral_comp_rev n f
  rw [h_int_eq, ← mul_assoc] at hW
  exact mul_right_cancel₀ (integral_jostSchwartz_ne_zero n) hW

theorem vladimirov_tubeWeakLocality (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    {η : ℂ} (hspec : SpectrumCondition W) (hP : PoincareCovariant R W)
    (hloc : WeakLocality η W) :
    TubeWeakLocality η (vladimirovTubeExtension R W hspec hP) := by
  intro n α z _hz
  change vladimirov_H W n α (-(z ∘ Fin.rev)) =
    η ^ (n * (n - 1) / 2) * vladimirov_H W n (α ∘ Fin.rev) z
  rw [vladimirov_H_eq_zero_eval hspec n α (-(z ∘ Fin.rev)),
      vladimirov_H_eq_zero_eval hspec n (α ∘ Fin.rev) z]
  exact vladimirov_H_zero_weakLocality hspec hloc n α

theorem global_weakLocality_of_tubeWeakLocality (R : HolomorphicLorentzRep ι)
    (W : WightmanFamily ι) {η : ℂ}
    (hspec : SpectrumCondition W) (hP : PoincareCovariant R W)
    (h_tloc : TubeWeakLocality η (vladimirovTubeExtension R W hspec hP))
    (n : ℕ) (α : Fin n → ι) (f f' : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    (hf' : ∀ x : Fin n → Fin 4 → ℝ, f' (fun i => x (Fin.rev i)) = f x) :
    W n α f = η ^ (n * (n - 1) / 2) * W n (α ∘ Fin.rev) f' := by
  have h_base := h_tloc n α (tubeBasePoint n) (tubeBasePoint_mem_forward_tube_n n)
  change vladimirov_H W n α (-(tubeBasePoint n ∘ Fin.rev)) =
    η ^ (n * (n - 1) / 2) * vladimirov_H W n (α ∘ Fin.rev) (tubeBasePoint n) at h_base
  rw [vladimirov_H_eq_zero_eval hspec n α (-(tubeBasePoint n ∘ Fin.rev)),
      vladimirov_H_eq_zero_eval hspec n (α ∘ Fin.rev) (tubeBasePoint n)] at h_base
  rw [W_n_eq_vladimirov_H_zero_mul_integral hspec n α f,
      W_n_eq_vladimirov_H_zero_mul_integral hspec n (α ∘ Fin.rev) f']
  have h_int : (∫ x, f x) = ∫ x, f' x := by
    have h_f_eq : (fun x : Fin n → Fin 4 → ℝ => f x) =
        (fun x => f' (fun i => x (Fin.rev i))) := by
      ext x
      exact (hf' x).symm
    rw [h_f_eq]
    exact integral_comp_rev n f'
  rw [h_base, h_int, mul_assoc]

theorem weakLocality_of_vladimirov_tubeWeakLocality (R : HolomorphicLorentzRep ι)
    (W : WightmanFamily ι) {η : ℂ}
    (hspec : SpectrumCondition W) (hP : PoincareCovariant R W)
    (h_tloc : TubeWeakLocality η (vladimirovTubeExtension R W hspec hP)) :
    WeakLocality η W := by
  intro n α f f' _hf_jost hf'
  exact global_weakLocality_of_tubeWeakLocality R W hspec hP h_tloc n α f f' hf'

theorem jost_theorem_vladimirov (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    {η : ℂ} (hspec : SpectrumCondition W) (hP : PoincareCovariant R W) :
    WeakLocality η W ↔ TubeWeakLocality η (vladimirovTubeExtension R W hspec hP) :=
  ⟨vladimirov_tubeWeakLocality R W hspec hP,
   weakLocality_of_vladimirov_tubeWeakLocality R W hspec hP⟩

theorem global_weakLocality_of_weakLocality (R : HolomorphicLorentzRep ι)
    (W : WightmanFamily ι) {η : ℂ}
    (hspec : SpectrumCondition W) (hP : PoincareCovariant R W)
    (hloc : WeakLocality η W)
    (n : ℕ) (α : Fin n → ι) (f f' : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    (hf' : ∀ x : Fin n → Fin 4 → ℝ, f' (fun i => x (Fin.rev i)) = f x) :
    W n α f = η ^ (n * (n - 1) / 2) * W n (α ∘ Fin.rev) f' :=
  global_weakLocality_of_tubeWeakLocality R W hspec hP
    (vladimirov_tubeWeakLocality R W hspec hP hloc) n α f f' hf'

lemma forward_tube_zero_mem : (0 : Fin 0 → Fin 4 → ℂ) ∈ forward_tube_n 0 :=
  fun i _ => Fin.elim0 i

lemma mem_orbit_domain_zero (Λ : SpecialSpecialComplexLorentzGroup) :
    Λ ∈ orbit_domain 0 0 :=
  fun i _ => Fin.elim0 i

lemma vector_bhw_diff_eq_of_const (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (E : TubeExtension W) (n : ℕ)
    (h_const : ∀ (α : Fin n → ι) (w : Fin n → Fin 4 → ℂ), E.H n α w = E.H n α 0)
    (w1 w2 : Fin n → Fin 4 → ℂ) (α : Fin n → ι) (x : Fin 6 → ℂ) :
    vector_bhw_diff R W E n w1 α x = vector_bhw_diff R W E n w2 α x := by
  unfold vector_bhw_diff
  simp_rw [h_const]

lemma local_nbhd_of_const (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (E : TubeExtension W) (h_cov : TubeCovariant R E) (n : ℕ)
    (h_const : ∀ (α : Fin n → ι) (w : Fin n → Fin 4 → ℂ), E.H n α w = E.H n α 0)
    (g1 : SL2C × SL2C) :
    ∀ᶠ Λ in 𝓝 (spinorPhi g1), ∃ x : Fin 6 → ℂ, Λ = spinorPhi (gcart x * g1) ∧
      ∀ α, vector_bhw_diff R W E n (spinorPhi g1 • tubeBasePoint n) α x = 0 := by
  have h_ev0 : ∀ᶠ x in 𝓝 (0 : Fin 6 → ℂ), ∀ α : Fin n → ι,
      vector_bhw_diff R W E n (tubeBasePoint n) α x = 0 :=
    Filter.eventually_all.mpr (fun α =>
      vector_bhw_diff_eq_zero_near_zero R W E h_cov n (tubeBasePoint n)
        (tubeBasePoint_mem_forward_tube_n n) α)
  have h_ev : ∀ᶠ x in 𝓝 (0 : Fin 6 → ℂ), ∀ α : Fin n → ι,
      vector_bhw_diff R W E n (spinorPhi g1 • tubeBasePoint n) α x = 0 := by
    apply Filter.Eventually.mono h_ev0
    intro x hx α
    rw [vector_bhw_diff_eq_of_const R W E n h_const _ (tubeBasePoint n)]
    exact hx α
  obtain ⟨U, hU, hUeq⟩ := eventually_iff_exists_mem.mp h_ev
  have h_img := local_chart_isOpenMap_at_zero U hU
  have h_mult : Tendsto (fun Λ : SpecialSpecialComplexLorentzGroup => Λ * (spinorPhi g1)⁻¹)
      (𝓝 (spinorPhi g1)) (𝓝 1) := by
    have h0 := (continuous_mul_const (spinorPhi g1)⁻¹ : Continuous
      (fun Λ : SpecialSpecialComplexLorentzGroup => Λ * (spinorPhi g1)⁻¹)).tendsto (spinorPhi g1)
    rwa [mul_inv_cancel] at h0
  filter_upwards [h_mult h_img] with Λ hΛ
  obtain ⟨x, hx, hxe⟩ := hΛ
  refine ⟨x, ?_, hUeq x hx⟩
  rw [map_mul, ← local_chart_eq, hxe, inv_mul_cancel_right]

lemma complex_covariance_of_const (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (E : TubeExtension W) (h_cov : TubeCovariant R E) (n : ℕ)
    (h_const : ∀ (α : Fin n → ι) (w : Fin n → Fin 4 → ℂ), E.H n α w = E.H n α 0)
    (A B : SL2C) (α : Fin n → ι) :
    E.H n α 0 = ∑ β : Fin n → ι, (∏ i, R.σ (A, B) (α i) (β i)) * E.H n β 0 := by
  let z := tubeBasePoint n
  have hz_tube : z ∈ forward_tube_n n := tubeBasePoint_mem_forward_tube_n n
  let D := orbit_domain 0 0
  have hD_conn : IsConnected D := is_connected_orbit_domain 0 0 forward_tube_zero_mem
  have hD_open : IsOpen D := orbit_domain_isOpen 0 0
  let u : Set SpecialSpecialComplexLorentzGroup :=
    {Λ | Λ ∈ D ∧ ∃ g, spinorPhi g = Λ ∧ ∀ α, dd R W E n z g α = 0}
  let v : Set SpecialSpecialComplexLorentzGroup := D \ u
  have hu_open : IsOpen u := by
    rw [isOpen_iff_mem_nhds]
    rintro Λ0 ⟨hΛ0D, g0, hg0, hd0⟩
    subst hg0
    have h_loc := local_nbhd_of_const R W E h_cov n h_const g0
    have h_D : D ∈ 𝓝 (spinorPhi g0) := hD_open.mem_nhds hΛ0D
    filter_upwards [h_loc, h_D] with Λ ⟨x, hΛx, hx0⟩ hD
    refine ⟨hD, gcart x * g0, hΛx.symm, ?_⟩
    intro α'
    rw [dd_mul]
    have h1 : E.H n α' (spinorPhi (gcart x) • (spinorPhi g0 • z)) -
        ∑ β, Tm R n (gcart x) α' β * E.H n β (spinorPhi g0 • z) =
        vector_bhw_diff R W E n (spinorPhi g0 • z) α' x := rfl
    rw [h1, hx0 α']
    simp [hd0]
  have hv_open : IsOpen v := by
    rw [isOpen_iff_mem_nhds]
    rintro Λ1 ⟨hΛ1D, hΛ1u⟩
    obtain ⟨g1, hg1⟩ := spinorPhi_surjective Λ1
    subst hg1
    have h_loc := local_nbhd_of_const R W E h_cov n h_const g1
    have h_D : D ∈ 𝓝 (spinorPhi g1) := hD_open.mem_nhds hΛ1D
    filter_upwards [h_loc, h_D] with Λ ⟨x, hΛx, hx0⟩ hD
    refine ⟨hD, ?_⟩
    rintro ⟨_, g', hg', hd'⟩
    apply hΛ1u
    refine ⟨hΛ1D, g1, rfl, ?_⟩
    have hphi : spinorPhi (gcart x * g1) = spinorPhi g' := by rw [← hΛx, hg']
    have hzero : ∀ α', dd R W E n z (gcart x * g1) α' = 0 := by
      intro α'
      rw [dd_eq_of_phi_eq R W E h_cov n z hz_tube _ _ hphi.symm α']
      exact hd' α'
    have hzero' : ∀ α', ∑ β, Tm R n (gcart x) α' β * dd R W E n z g1 β = 0 := by
      intro α'
      have := hzero α'
      rw [dd_mul] at this
      have h1 : E.H n α' (spinorPhi (gcart x) • (spinorPhi g1 • z)) -
          ∑ β, Tm R n (gcart x) α' β * E.H n β (spinorPhi g1 • z) =
          vector_bhw_diff R W E n (spinorPhi g1 • z) α' x := rfl
      rw [h1, hx0 α', zero_add] at this
      exact this
    exact Tm_injective R n (gcart x) _ hzero'
  have huv : Disjoint u v := by
    rw [Set.disjoint_iff]
    rintro Λ ⟨hu, hv⟩
    exact hv.2 hu
  have h_union : D ⊆ u ∪ v := by
    intro Λ hΛ
    by_cases h : Λ ∈ u
    · exact Or.inl h
    · exact Or.inr ⟨hΛ, h⟩
  have h_nonempty : (D ∩ u).Nonempty := by
    have h1 : (1 : SpecialSpecialComplexLorentzGroup) ∈ D := mem_orbit_domain_zero 1
    refine ⟨1, h1, h1, 1, map_one _, ?_⟩
    intro α'
    unfold dd
    have e : (1 : SpecialSpecialComplexLorentzGroup) • z = z := one_smul _ z
    rw [map_one, e]
    simp [Tm_one]
  have h_sub : D ⊆ u :=
    hD_conn.isPreconnected.subset_left_of_subset_union hu_open hv_open huv h_union h_nonempty
  have hmem : spinorPhi (A, B) ∈ u := h_sub (mem_orbit_domain_zero (spinorPhi (A, B)))
  obtain ⟨_, g, hg, hd⟩ := hmem
  have h_dd := dd_eq_of_phi_eq R W E h_cov n z hz_tube g (A, B) hg α
  rw [hd α] at h_dd
  unfold dd Tm at h_dd
  have h_eq := sub_eq_zero.mp h_dd
  simp_rw [h_const] at h_eq
  exact h_eq

theorem vladimirov_H_zero_complexCovariant (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (hspec : SpectrumCondition W) (hP : PoincareCovariant R W)
    (n : ℕ) (A B : SL2C) (α : Fin n → ι) :
    vladimirov_H W n α 0 =
      ∑ β : Fin n → ι, (∏ i, R.σ (A, B) (α i) (β i)) * vladimirov_H W n β 0 :=
  complex_covariance_of_const R W
    (vladimirovTubeExtension R W hspec hP)
    (vladimirov_tubeCovariant R W hspec hP)
    n (vladimirov_H_eq_zero_eval hspec n) A B α

theorem vladimirov_H_complexCovariant_all (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (hspec : SpectrumCondition W) (hP : PoincareCovariant R W)
    (n : ℕ) (A B : SL2C) (z w : Fin n → Fin 4 → ℂ) (α : Fin n → ι) :
    vladimirov_H W n α z =
      ∑ β : Fin n → ι, (∏ i, R.σ (A, B) (α i) (β i)) * vladimirov_H W n β w := by
  rw [vladimirov_H_eq_zero_eval hspec n α z]
  simp_rw [vladimirov_H_eq_zero_eval hspec n _ w]
  exact vladimirov_H_zero_complexCovariant R W hspec hP n A B α

def revIndexEquiv (n : ℕ) (ι : Type*) : (Fin n → ι) ≃ (Fin n → ι) where
  toFun β := β ∘ Fin.rev
  invFun β := β ∘ Fin.rev
  left_inv β := by ext i; simp [Fin.rev_rev]
  right_inv β := by ext i; simp [Fin.rev_rev]

omit [Fintype ι] [DecidableEq ι] in
lemma prod_rev_comp (n : ℕ) (M : ι → ι → ℂ) (α β : Fin n → ι) :
    (∏ i : Fin n, M (α (Fin.rev i)) (β (Fin.rev i))) = ∏ i : Fin n, M (α i) (β i) :=
  Equiv.prod_comp Fin.revPerm (fun i => M (α i) (β i))

omit [DecidableEq ι] in
lemma sum_prod_revIndex (n : ℕ) (M : ι → ι → ℂ) (F : (Fin n → ι) → ℂ) (α : Fin n → ι) :
    (∑ β : Fin n → ι, (∏ i : Fin n, M ((α ∘ Fin.rev) i) (β i)) * F β) =
      ∑ β : Fin n → ι, (∏ i : Fin n, M (α i) (β i)) * F (β ∘ Fin.rev) := by
  rw [← (revIndexEquiv n ι).sum_comp]
  apply Finset.sum_congr rfl
  intro β _
  change (∏ i : Fin n, M (α (Fin.rev i)) (β (Fin.rev i))) * F (β ∘ Fin.rev) =
    (∏ i : Fin n, M (α i) (β i)) * F (β ∘ Fin.rev)
  rw [prod_rev_comp n M α β]

theorem tube_pct_theorem (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    {η : ℂ} (E : TubeExtension W)
    (h_ccov : ComplexCovariant R E) (h_tloc : TubeWeakLocality η E)
    (n : ℕ) (z : Fin n → Fin 4 → ℂ)
    (hz : z ∈ forward_tube_n n) (h_neg_z : -z ∈ forward_tube_n n)
    (α : Fin n → ι) :
    E.H n α (-(z ∘ Fin.rev)) =
      η ^ (n * (n - 1) / 2) *
        ∑ β : Fin n → ι, (∏ i, R.σ (-1, 1) (α i) (β i)) * E.H n (β ∘ Fin.rev) (-z) := by
  have h_loc := h_tloc n α z hz
  have h_neg_neg : -(-z) = z := neg_neg z
  have hz_nn : -(-z) ∈ forward_tube_n n := by
    rwa [h_neg_neg]
  have h_cov := complexCovariant_neg_one_one R E h_ccov n (-z) h_neg_z hz_nn (α ∘ Fin.rev)
  rw [h_neg_neg] at h_cov
  rw [h_loc, h_cov,
      sum_prod_revIndex n (fun a b => R.σ (-1, 1) a b) (fun β => E.H n β (-z)) α]

theorem vladimirov_tube_pct_theorem (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    {η : ℂ} (hspec : SpectrumCondition W) (hP : PoincareCovariant R W)
    (hloc : WeakLocality η W)
    (n : ℕ) (z : Fin n → Fin 4 → ℂ) (hz : z ∈ forward_tube_n n) (α : Fin n → ι) :
    vladimirov_H W n α (-(z ∘ Fin.rev)) =
      η ^ (n * (n - 1) / 2) *
        ∑ β : Fin n → ι,
          (∏ i, R.σ (-1, 1) (α i) (β i)) * vladimirov_H W n (β ∘ Fin.rev) z := by
  have h_loc := vladimirov_tubeWeakLocality R W hspec hP hloc n α z hz
  change vladimirov_H W n α (-(z ∘ Fin.rev)) =
    η ^ (n * (n - 1) / 2) * vladimirov_H W n (α ∘ Fin.rev) z at h_loc
  rw [h_loc,
      vladimirov_H_complexCovariant_all R W hspec hP n (-1) 1 z z (α ∘ Fin.rev),
      sum_prod_revIndex n (fun a b => R.σ (-1, 1) a b) (fun β => vladimirov_H W n β z) α]

def WightmanPCT (η : ℂ) (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι) : Prop :=
  ∀ (n : ℕ) (α : Fin n → ι) (f f' : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ),
    (∀ x : Fin n → Fin 4 → ℝ, f' (fun i => -x (Fin.rev i)) = f x) →
    W n α f =
      η ^ (n * (n - 1) / 2) *
        ∑ β : Fin n → ι, (∏ i, R.σ (-1, 1) (α i) (β i)) * W n (β ∘ Fin.rev) f'

theorem wightman_pct_theorem (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    {η : ℂ} (hspec : SpectrumCondition W) (hP : PoincareCovariant R W)
    (hloc : WeakLocality η W) :
    WightmanPCT η R W := by
  intro n α f f' hf'
  have h_pct_z := vladimirov_tube_pct_theorem R W hspec hP hloc n
    (tubeBasePoint n) (tubeBasePoint_mem_forward_tube_n n) α
  rw [vladimirov_H_eq_zero_eval hspec n α (-(tubeBasePoint n ∘ Fin.rev))] at h_pct_z
  simp_rw [vladimirov_H_eq_zero_eval hspec n _ (tubeBasePoint n)] at h_pct_z
  rw [W_n_eq_vladimirov_H_zero_mul_integral hspec n α f]
  simp_rw [W_n_eq_vladimirov_H_zero_mul_integral hspec n _ f']
  have h_int : (∫ x, f x) = ∫ x, f' x := by
    have h_f_eq : (fun x : Fin n → Fin 4 → ℝ => f x) =
        (fun x => f' (fun i => -x (Fin.rev i))) := by
      ext x
      exact (hf' x).symm
    rw [h_f_eq]
    exact integral_comp_pct n f'
  rw [h_pct_z, h_int, mul_assoc, Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro β _
  ring

theorem weakLocality_of_wightman_pct (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    {η : ℂ} (hspec : SpectrumCondition W) (hP : PoincareCovariant R W)
    (hpct : WightmanPCT η R W) :
    WeakLocality η W := by
  apply weakLocality_of_vladimirov_tubeWeakLocality R W hspec hP
  intro n α z _hz
  change vladimirov_H W n α (-(z ∘ Fin.rev)) =
    η ^ (n * (n - 1) / 2) * vladimirov_H W n (α ∘ Fin.rev) z
  rw [vladimirov_H_eq_zero_eval hspec n α (-(z ∘ Fin.rev)),
      vladimirov_H_eq_zero_eval hspec n (α ∘ Fin.rev) z]
  let f := jostSchwartz n
  let f' := schwartzPCTCLM n f
  have hf'_pct : ∀ x : Fin n → Fin 4 → ℝ, f' (fun i => -x (Fin.rev i)) = f x := by
    intro x
    dsimp [f']
    congr 1
    ext i k
    simp [Fin.rev_rev]
  have hW := hpct n α f f' hf'_pct
  rw [W_n_eq_vladimirov_H_zero_mul_integral hspec n α f] at hW
  simp_rw [W_n_eq_vladimirov_H_zero_mul_integral hspec n _ f'] at hW
  have h_int_eq : (∫ x, f' x) = ∫ x, f x :=
    integral_comp_pct n f
  rw [h_int_eq] at hW
  have h_factor :
      (∑ β : Fin n → ι,
        (∏ i, R.σ (-1, 1) (α i) (β i)) * (vladimirov_H W n (β ∘ Fin.rev) 0 * ∫ x, f x)) =
      (∑ β : Fin n → ι,
        (∏ i, R.σ (-1, 1) (α i) (β i)) * vladimirov_H W n (β ∘ Fin.rev) 0) * ∫ x, f x := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro β _
    ring
  rw [h_factor, ← mul_assoc] at hW
  have h_cancel := mul_right_cancel₀ (integral_jostSchwartz_ne_zero n) hW
  have h_cov := vladimirov_H_zero_complexCovariant R W hspec hP n (-1) 1 (α ∘ Fin.rev)
  rw [sum_prod_revIndex n (fun a b => R.σ (-1, 1) a b) (fun β => vladimirov_H W n β 0) α] at h_cov
  rw [h_cancel, ← h_cov]

theorem wightman_pct_iff_weakLocality (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    {η : ℂ} (hspec : SpectrumCondition W) (hP : PoincareCovariant R W) :
    WeakLocality η W ↔ WightmanPCT η R W :=
  ⟨wightman_pct_theorem R W hspec hP, weakLocality_of_wightman_pct R W hspec hP⟩

lemma sigma_pt_mul_sigma_tp (R : HolomorphicLorentzRep ι) :
    R.σ (-1, 1) * R.σ (1, -1) = R.σ (-1, -1) := by
  rw [← map_mul]
  congr 1
  ext <;> simp

lemma sigma_tp_mul_sigma_pt (R : HolomorphicLorentzRep ι) :
    R.σ (1, -1) * R.σ (-1, 1) = R.σ (-1, -1) := by
  rw [← map_mul]
  congr 1
  ext <;> simp

theorem sigma_pt_mul_sigma_tp_eq_spinParity (R : HolomorphicLorentzRep ι) (ε : ℂ)
    (hε : R.HasSpinParity ε) :
    R.σ (-1, 1) * R.σ (1, -1) = ε • (1 : Matrix ι ι ℂ) := by
  rw [sigma_pt_mul_sigma_tp, hε.1]

theorem sigma_tp_mul_sigma_pt_eq_spinParity (R : HolomorphicLorentzRep ι) (ε : ℂ)
    (hε : R.HasSpinParity ε) :
    R.σ (1, -1) * R.σ (-1, 1) = ε • (1 : Matrix ι ι ℂ) := by
  rw [sigma_tp_mul_sigma_pt, hε.1]

lemma starStructure_intertwine_pt {R : HolomorphicLorentzRep ι} (S : StarStructure R) :
    S.C * R.σ (-1, 1) = (R.σ (1, -1)).map star * S.C := by
  have h := S.intertwine (-1) 1
  have h1 : sl2c_conj (1 : SL2C) = 1 := sl2c_conj_one
  have h2 : sl2c_conj (-1 : SL2C) = -1 := by
    apply Subtype.ext; ext i j; fin_cases i <;> fin_cases j <;> simp [sl2c_conj]
  rwa [h1, h2] at h

lemma two_mul_two_sub_one_div_two : 2 * (2 - 1) / 2 = 1 := rfl

omit [Fintype ι] [DecidableEq ι] in
lemma tubeWeakLocality_two {W : WightmanFamily ι} {η : ℂ} {E : TubeExtension W}
    (h_tloc : TubeWeakLocality η E)
    (α : Fin 2 → ι) (z : Fin 2 → Fin 4 → ℂ) (hz : z ∈ forward_tube_n 2) :
    E.H 2 α (-(z ∘ Fin.rev)) = η * E.H 2 (α ∘ Fin.rev) z := by
  have h := h_tloc 2 α z hz
  rwa [two_mul_two_sub_one_div_two, pow_one] at h

omit [Fintype ι] [DecidableEq ι] in
lemma weakLocality_two {W : WightmanFamily ι} {η : ℂ}
    (hloc : WeakLocality η W)
    (α : Fin 2 → ι) (f f' : SchwartzMap (Fin 2 → Fin 4 → ℝ) ℂ)
    (hf_jost : ∀ x, f x ≠ 0 → x ∈ jost_points_n 2)
    (hf'_rev : ∀ x : Fin 2 → Fin 4 → ℝ, f' (fun i => x (Fin.rev i)) = f x) :
    W 2 α f = η * W 2 (α ∘ Fin.rev) f' := by
  have h := hloc 2 α f f' hf_jost hf'_rev
  rwa [two_mul_two_sub_one_div_two, pow_one] at h

def TwoPointSpinExchange (ε : ℂ) {W : WightmanFamily ι} (E : TubeExtension W) : Prop :=
  ∀ (α : Fin 2 → ι) (z : Fin 2 → Fin 4 → ℂ),
    z ∈ forward_tube_n 2 →
    E.H 2 α (-(z ∘ Fin.rev)) = ε * E.H 2 (α ∘ Fin.rev) z

def DistributionalTwoPointSpinExchange (ε : ℂ) (W : WightmanFamily ι) : Prop :=
  ∀ (α : Fin 2 → ι) (f f' : SchwartzMap (Fin 2 → Fin 4 → ℝ) ℂ),
    (∀ x, f x ≠ 0 → x ∈ jost_points_n 2) →
    (∀ x : Fin 2 → Fin 4 → ℝ, f' (fun i => x (Fin.rev i)) = f x) →
    W 2 α f = ε * W 2 (α ∘ Fin.rev) f'

lemma twoPointSpinExchange_of_scalar_pt (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (E : TubeExtension W) (h_ccov : ComplexCovariant R E)
    (δ ε : ℂ) (hδ : R.σ (-1, 1) = δ • (1 : Matrix ι ι ℂ)) (hδ_sq : δ ^ 2 = ε)
    (h_symm : ∀ (α : Fin 2 → ι) (z : Fin 2 → Fin 4 → ℂ),
      z ∈ forward_tube_n 2 → -z ∈ forward_tube_n 2 →
      E.H 2 α (-(z ∘ Fin.rev)) = E.H 2 (α ∘ Fin.rev) (-z))
    (α : Fin 2 → ι) (z : Fin 2 → Fin 4 → ℂ)
    (hz : z ∈ forward_tube_n 2) (h_neg_z : -z ∈ forward_tube_n 2) :
    E.H 2 α (-(z ∘ Fin.rev)) = ε * E.H 2 (α ∘ Fin.rev) z := by
  rw [h_symm α z hz h_neg_z]
  have h_cov := complexCovariant_neg_one_one R E h_ccov 2 z hz h_neg_z (α ∘ Fin.rev)
  rw [h_cov]
  have h_prod : ∀ β : Fin 2 → ι,
      (∏ i : Fin 2, R.σ (-1, 1) ((α ∘ Fin.rev) i) (β i)) =
        if α ∘ Fin.rev = β then ε else 0 := by
    intro β
    rw [hδ]
    by_cases h : α ∘ Fin.rev = β
    · subst h
      simp only [↓reduceIte, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
        Finset.prod_const, Finset.card_univ, Fintype.card_fin, hδ_sq]
    · rw [if_neg h]
      obtain ⟨i, hi⟩ : ∃ i, (α ∘ Fin.rev) i ≠ β i := by
        by_contra hc
        push Not at hc
        exact h (funext hc)
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      have h_one : (1 : Matrix ι ι ℂ) ((α ∘ Fin.rev) i) (β i) = 0 :=
        Matrix.one_apply_ne hi
      rw [Matrix.smul_apply, h_one, smul_zero]
  simp_rw [h_prod]
  simp

theorem spin_statistics_theorem_tube (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    {η ε : ℂ} (E : TubeExtension W)
    (_hε : R.HasSpinParity ε)
    (h_tloc : TubeWeakLocality η E)
    (h_exch : TwoPointSpinExchange ε E)
    (h_nondeg : ∃ (α : Fin 2 → ι) (z : Fin 2 → Fin 4 → ℂ),
      z ∈ forward_tube_n 2 ∧ E.H 2 (α ∘ Fin.rev) z ≠ 0) :
    η = ε := by
  obtain ⟨α, z, hz, h_ne⟩ := h_nondeg
  have h1 := tubeWeakLocality_two h_tloc α z hz
  have h2 := h_exch α z hz
  have h_eq : η * E.H 2 (α ∘ Fin.rev) z = ε * E.H 2 (α ∘ Fin.rev) z := by
    rw [← h1, ← h2]
  exact mul_right_cancel₀ h_ne h_eq

theorem wrong_statistics_two_point_eq_zero_tube (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    {η ε : ℂ} (E : TubeExtension W)
    (hε : R.HasSpinParity ε)
    (h_tloc : TubeWeakLocality η E)
    (h_exch : TwoPointSpinExchange ε E)
    (h_wrong : η ≠ ε)
    (α : Fin 2 → ι) (z : Fin 2 → Fin 4 → ℂ) (hz : z ∈ forward_tube_n 2) :
    E.H 2 α z = 0 := by
  by_contra h_ne
  apply h_wrong
  apply spin_statistics_theorem_tube R W E hε h_tloc h_exch
  refine ⟨α ∘ Fin.rev, z, hz, ?_⟩
  have h_rev : (α ∘ Fin.rev) ∘ Fin.rev = α := by
    ext i
    simp [Fin.rev_rev]
  rwa [h_rev]

theorem spin_statistics_theorem (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    {η ε : ℂ} (_hε : R.HasSpinParity ε)
    (hloc : WeakLocality η W)
    (h_exch : DistributionalTwoPointSpinExchange ε W)
    (h_nondeg : ∃ (α : Fin 2 → ι) (f f' : SchwartzMap (Fin 2 → Fin 4 → ℝ) ℂ),
      (∀ x, f x ≠ 0 → x ∈ jost_points_n 2) ∧
      (∀ x : Fin 2 → Fin 4 → ℝ, f' (fun i => x (Fin.rev i)) = f x) ∧
      W 2 (α ∘ Fin.rev) f' ≠ 0) :
    η = ε := by
  obtain ⟨α, f, f', hf_jost, hf'_rev, h_ne⟩ := h_nondeg
  have h1 := weakLocality_two hloc α f f' hf_jost hf'_rev
  have h2 := h_exch α f f' hf_jost hf'_rev
  have h_eq : η * W 2 (α ∘ Fin.rev) f' = ε * W 2 (α ∘ Fin.rev) f' := by
    rw [← h1, ← h2]
  exact mul_right_cancel₀ h_ne h_eq

theorem wrong_statistics_two_point_eq_zero_distributional
    (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    {η ε : ℂ} (hε : R.HasSpinParity ε)
    (hloc : WeakLocality η W)
    (h_exch : DistributionalTwoPointSpinExchange ε W)
    (h_wrong : η ≠ ε)
    (α : Fin 2 → ι) (f f' : SchwartzMap (Fin 2 → Fin 4 → ℝ) ℂ)
    (hf_jost : ∀ x, f x ≠ 0 → x ∈ jost_points_n 2)
    (hf'_rev : ∀ x : Fin 2 → Fin 4 → ℝ, f' (fun i => x (Fin.rev i)) = f x) :
    W 2 (α ∘ Fin.rev) f' = 0 := by
  by_contra h_ne
  apply h_wrong
  exact spin_statistics_theorem R W hε hloc h_exch ⟨α, f, f', hf_jost, hf'_rev, h_ne⟩

theorem spin_statistics_trivialRep (W : WightmanFamily Unit) {η : ℂ}
    (E : TubeExtension W)
    (h_tloc : TubeWeakLocality η E)
    (h_exch : TwoPointSpinExchange 1 E)
    (h_nondeg : ∃ (α : Fin 2 → Unit) (z : Fin 2 → Fin 4 → ℂ),
      z ∈ forward_tube_n 2 ∧ E.H 2 (α ∘ Fin.rev) z ≠ 0) :
    η = 1 :=
  spin_statistics_theorem_tube trivialRep W E trivialRep_spinParity h_tloc h_exch h_nondeg

theorem spin_statistics_stdRep (W : WightmanFamily (Fin 4)) {η : ℂ}
    (E : TubeExtension W)
    (h_tloc : TubeWeakLocality η E)
    (h_exch : TwoPointSpinExchange 1 E)
    (h_nondeg : ∃ (α : Fin 2 → Fin 4) (z : Fin 2 → Fin 4 → ℂ),
      z ∈ forward_tube_n 2 ∧ E.H 2 (α ∘ Fin.rev) z ≠ 0) :
    η = 1 :=
  spin_statistics_theorem_tube stdRep W E stdRep_spinParity h_tloc h_exch h_nondeg

theorem spin_statistics_leftWeylRep (W : WightmanFamily (Fin 2)) {η : ℂ}
    (E : TubeExtension W)
    (h_tloc : TubeWeakLocality η E)
    (h_exch : TwoPointSpinExchange (-1) E)
    (h_nondeg : ∃ (α : Fin 2 → Fin 2) (z : Fin 2 → Fin 4 → ℂ),
      z ∈ forward_tube_n 2 ∧ E.H 2 (α ∘ Fin.rev) z ≠ 0) :
    η = -1 :=
  spin_statistics_theorem_tube leftWeylRep W E leftWeylRep_spinParity h_tloc h_exch h_nondeg

end QFT
