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
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → E → ℂ) (x : E)
    (hf : ∀ i ∈ s, AnalyticAt ℂ (f i) x) :
    AnalyticAt ℂ (fun e => ∑ i ∈ s, f i e) x := by
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
    {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → E → ℂ) (x : E)
    (hf : ∀ i, AnalyticAt ℂ (f i) x) :
    AnalyticAt ℂ (fun e => ∑ i : ι, f i e) x := by
  exact finset_sum_analyticAt Finset.univ f x (fun i _ => hf i)

lemma fintype_prod_analyticAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → E → ℂ) (x : E)
    (hf : ∀ i, AnalyticAt ℂ (f i) x) :
    AnalyticAt ℂ (fun e => ∏ i : ι, f i e) x := by
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
      R.σ (A, B) α β) = fun x => MvPolynomial.eval (fun i => Sum.elim (fun a => (sl2c_chart_invFun (local_chart_e x).1).1 a.1 a.2) (fun a => (sl2c_chart_invFun (local_chart_e x).2).1 a.1 a.2) i) P := by
    ext x
    exact hP (sl2c_chart_invFun (local_chart_e x).1, sl2c_chart_invFun (local_chart_e x).2)
  rw [h_eq]
  apply mvPolynomial_eval_analyticAt
  intro i
  rcases i with a | a
  · have h1 : AnalyticAt ℂ (fun x => (local_chart_e x).1) 0 :=
      ContinuousLinearMap.analyticAt (ContinuousLinearMap.fst ℂ (Fin 3 → ℂ) (Fin 3 → ℂ) ∘L local_chart_e.toContinuousLinearMap) 0
    have h2 := sl2c_chart_invFun_analytic
    have h0 : (local_chart_e 0).1 = 0 := by ext i; simp [local_chart_e]
    have hA : AnalyticAt ℂ (fun x => (sl2c_chart_invFun (local_chart_e x).1).1) 0 :=
      AnalyticAt.comp (g := fun a => (sl2c_chart_invFun a).1) (f := fun x => (local_chart_e x).1) (h0 ▸ h2) h1
    exact analyticAt_matrix_elem hA a.1 a.2
  · have h1 : AnalyticAt ℂ (fun x => (local_chart_e x).2) 0 :=
      ContinuousLinearMap.analyticAt (ContinuousLinearMap.snd ℂ (Fin 3 → ℂ) (Fin 3 → ℂ) ∘L local_chart_e.toContinuousLinearMap) 0
    have h2 := sl2c_chart_invFun_analytic
    have h0 : (local_chart_e 0).2 = 0 := by ext i; simp [local_chart_e]
    have hB : AnalyticAt ℂ (fun x => (sl2c_chart_invFun (local_chart_e x).2).1) 0 :=
      AnalyticAt.comp (g := fun a => (sl2c_chart_invFun a).1) (f := fun x => (local_chart_e x).2) (h0 ▸ h2) h1
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

  have h2 : AnalyticAt ℂ (fun x => ∑ β : Fin n → ι, (∏ i, R.σ (sl2c_chart_invFun (local_chart_e x).1, sl2c_chart_invFun (local_chart_e x).2) (α i) (β i)) * E.H n β z) 0 := by
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
  have h_eq_sum : ∑ β : Fin n → ι, (∏ i : Fin n, R.rep A (α i) (β i)) * E.H n β z = ∑ β : Fin n → ι, (∏ i : Fin n, R.σ (A, B) (α i) (β i)) * E.H n β z := by
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
    have H2 : (fun x => ((local_chart x) • z) i j) = fun x => ∑ k : Fin 4, (local_chart x).1.1 j k * z i k := by
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
    ContinuousLinearMap.pi (fun i => ContinuousLinearMap.comp Complex.ofRealCLM (ContinuousLinearMap.proj i))
  have h_ofReal : ∀ x : Fin 6 → ℝ, my_ofRealN x = (fun i => (x i : ℂ)) := fun _ => rfl

  have h_cont_R : ContinuousAt (fun x : Fin 6 → ℝ => local_chart (fun i => (x i : ℂ)) • z) 0 := by
    have h_comp : (fun x : Fin 6 → ℝ => local_chart (fun i => (x i : ℂ)) • z) = (fun x => local_chart x • z) ∘ my_ofRealN := rfl
    rw [h_comp]
    apply ContinuousAt.comp
    · exact local_chart_action_continuous n z
    · exact my_ofRealN.continuous.continuousAt

  have h_tube_nhds : ∀ᶠ x : Fin 6 → ℝ in 𝓝 0, local_chart (fun i => (x i : ℂ)) • z ∈ forward_tube_n n := by
    have h_open := forward_tube_n_isOpen n
    have hz0 : (fun i => ((0 : Fin 6 → ℝ) i : ℂ)) = 0 := by ext i; simp
    have h0 : local_chart (fun i => ((0 : Fin 6 → ℝ) i : ℂ)) • z = z := by
      rw [hz0]
      have h1 : local_chart 0 = 1 := local_chart_zero
      rw [h1]
      exact one_smul _ z
    have hz_nhds : forward_tube_n n ∈ 𝓝 z := h_open.mem_nhds hz
    have h0' : (fun (x : Fin 6 → ℝ) => local_chart (fun i => (x i : ℂ)) • z) 0 = z := h0
    have hz_nhds' : forward_tube_n n ∈ 𝓝 ((fun (x : Fin 6 → ℝ) => local_chart (fun i => (x i : ℂ)) • z) 0) := by
      rw [h0']
      exact hz_nhds
    exact h_cont_R.preimage_mem_nhds hz_nhds'

  have h_real_eq : ∀ᶠ x : Fin 6 → ℝ in 𝓝 0, vector_bhw_diff R W E n z α (fun i => (x i : ℂ)) = 0 := by
    apply Filter.Eventually.mono h_tube_nhds
    intro x hx
    exact vector_bhw_diff_eq_zero_on_real R W E h_cov n z hz α x hx

  have h_real_eq2 : ∀ᶠ x : Fin 6 → ℝ in 𝓝 0, vector_bhw_diff R W E n z α (my_ofRealN x) = (fun _ => (0 : ℂ)) (my_ofRealN x) := by
    apply Filter.Eventually.mono h_real_eq
    intro x hx
    rw [h_ofReal]
    exact hx

  exact Analysis.analytic_nhds_eq_of_real_eq_N (vector_bhw_diff R W E n z α) (fun _ => 0) 0 my_ofRealN h_ofReal hF_analytic hG_analytic h_real_eq2

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
  have h_prod : ∀ β : Fin n → ι, ∏ i, R.σ (-A, -B) (α i) (β i) = ∏ i, ∑ k_i : ι, R.σ (A, B) (α i) k_i * R.σ (-1, -1) k_i (β i) := by
    intro β
    apply Finset.prod_congr rfl
    intro i _
    exact congr_fun (congr_fun h_sigma (α i)) (β i)
  have h_sum_prod : ∀ β : Fin n → ι, (∏ i, ∑ k_i : ι, R.σ (A, B) (α i) k_i * R.σ (-1, -1) k_i (β i)) =
      ∑ k : Fin n → ι, ∏ i, (R.σ (A, B) (α i) (k i) * R.σ (-1, -1) (k i) (β i)) := by
    intro β
    exact Finset.prod_univ_sum (fun _ => (Finset.univ : Finset ι)) (fun i k_i => R.σ (A, B) (α i) k_i * R.σ (-1, -1) k_i (β i))
  calc
    ∑ β, (∏ i, R.σ (-A, -B) (α i) (β i)) * E.H n β z
      = ∑ β, (∑ k : Fin n → ι, ∏ i, R.σ (A, B) (α i) (k i) * R.σ (-1, -1) (k i) (β i)) * E.H n β z := by
        apply Finset.sum_congr rfl
        intro β _
        rw [h_prod β, h_sum_prod β]
    _ = ∑ β, ∑ k : Fin n → ι, (∏ i, R.σ (A, B) (α i) (k i) * R.σ (-1, -1) (k i) (β i)) * E.H n β z := by
        apply Finset.sum_congr rfl
        intro β _
        exact Finset.sum_mul _ _ _
    _ = ∑ k : Fin n → ι, ∑ β, (∏ i, R.σ (A, B) (α i) (k i) * R.σ (-1, -1) (k i) (β i)) * E.H n β z := by
        exact Finset.sum_comm
    _ = ∑ k : Fin n → ι, ∑ β, (∏ i, R.σ (A, B) (α i) (k i)) * (∏ i, R.σ (-1, -1) (k i) (β i)) * E.H n β z := by
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro β _
        rw [Finset.prod_mul_distrib]
    _ = ∑ k : Fin n → ι, (∏ i, R.σ (A, B) (α i) (k i)) * ∑ β, (∏ i, R.σ (-1, -1) (k i) (β i)) * E.H n β z := by
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

lemma spinor_action_eq_self_imp (A B : SL2C) (h : spinorPhi (A, B) = 1) (X : Matrix (Fin 2) (Fin 2) ℂ) :
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
  have hBA : B.1ᵀ * A.1 = 1 := Matrix.mul_eq_one_comm.mp hAB
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
    have := congrFun (congrFun e1 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two] at this
    first | exact this | exact this.symm
  have hc : A.1 1 0 = 0 := by
    have := congrFun (congrFun e1 1) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two] at this
    first | exact this | exact this.symm
  have had : A.1 0 0 = A.1 1 1 := by
    have := congrFun (congrFun e2 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two, hc] at this
    first | exact this | exact this.symm
  set a := A.1 0 0 with ha
  have haa : a * a = 1 := by
    rw [hb, hc, ← had] at hdet
    simpa using hdet
  have hA' : A.1 = !![a, 0; 0, a] := by
    rw [Matrix.eta_fin_two A.1, hb, hc, ← had]
  have hB00 : B.1 0 0 = a := by
    have := congrFun (congrFun hAB 0) 0
    rw [hA'] at this
    simp [Matrix.mul_apply, Fin.sum_univ_two] at this
    calc B.1 0 0 = (a * a) * B.1 0 0 := by rw [haa, one_mul]
      _ = a * (a * B.1 0 0) := by ring
      _ = a := by rw [this, mul_one]
  have hB11 : B.1 1 1 = a := by
    have := congrFun (congrFun hAB 1) 1
    rw [hA'] at this
    simp [Matrix.mul_apply, Fin.sum_univ_two] at this
    calc B.1 1 1 = (a * a) * B.1 1 1 := by rw [haa, one_mul]
      _ = a * (a * B.1 1 1) := by ring
      _ = a := by rw [this, mul_one]
  have hB01 : B.1 0 1 = 0 := by
    have := congrFun (congrFun hAB 1) 0
    rw [hA'] at this
    simp [Matrix.mul_apply, Fin.sum_univ_two] at this
    rcases this with h0 | h0
    · have : a ≠ 0 := by intro h0'; rw [h0'] at haa; simp at haa
      exact absurd h0 this
    · exact h0
  have hB10 : B.1 1 0 = 0 := by
    have := congrFun (congrFun hAB 0) 1
    rw [hA'] at this
    simp [Matrix.mul_apply, Fin.sum_univ_two] at this
    rcases this with h0 | h0
    · have : a ≠ 0 := by intro h0'; rw [h0'] at haa; simp at haa
      exact absurd h0 this
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

noncomputable def Tm (R : HolomorphicLorentzRep ι) (n : ℕ) (g : SL2C × SL2C) (α β : Fin n → ι) : ℂ :=
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
      push_neg at hc
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
    have key : ∀ β, ∑ α, Tm R n g⁻¹ γ α * (Tm R n g α β * v β) = (if γ = β then 1 else 0) * v β := by
      intro β
      rw [← Tm_one, ← inv_mul_cancel g, Tm_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro α _
      ring
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
  have h_sub : D ⊆ u := hD_conn.isPreconnected.subset_left_of_subset_union hu_open hv_open huv h_union h_nonempty
  have hmem : spinorPhi (A, B) ∈ u := h_sub hz_trans
  obtain ⟨_, g, hg, hd⟩ := hmem
  have := dd_eq_of_phi_eq R W E h_cov n z hz_tube g (A, B) hg α
  rw [hd α] at this
  unfold dd Tm at this
  exact sub_eq_zero.mp this


end QFT
