import OSReconstruction

namespace QFT

open Geometry Geometry.MatrixAnalysis Geometry.PolarDecomposition
  MeasureTheory Filter Topology Matrix
open scoped ComplexOrder FourierTransform RealInnerProductSpace
  Interval ContDiff InnerProductSpace

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def vacS : SchwingerFamily ι
  | 0, _, _ => 1
  | _ + 1, _, _ => 0

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma vacS_zero (α : Fin 0 → ι) (x : Fin 0 → Fin 4 → ℝ) :
    vacS 0 α x = 1 := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma vacS_succ (n : ℕ) (α : Fin (n + 1) → ι) (x : Fin (n + 1) → Fin 4 → ℝ) :
    vacS (n + 1) α x = 0 := rfl

omit [Fintype ι] [DecidableEq ι] in
lemma vacS_of_one_le {n : ℕ} (hn : 1 ≤ n) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ) :
    vacS n α x = 0 := by
  cases n with
  | zero => omega
  | succ m => rfl

omit [Fintype ι] [DecidableEq ι] in
theorem vacS_vacuumNormalized : OSVacuumNormalized (vacS (ι := ι)) := rfl

noncomputable def vacW : WightmanFamily ι
  | 0, _ => TemperedDistribution.delta (0 : Fin 0 → Fin 4 → ℝ)
  | _ + 1, _ => 0

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma vacW_zero_apply (α : Fin 0 → ι) (f : SchwartzMap (Fin 0 → Fin 4 → ℝ) ℂ) :
    vacW 0 α f = f 0 := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma vacW_succ (n : ℕ) (α : Fin (n + 1) → ι) :
    vacW (n + 1) α = 0 := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma vacW_succ_apply (n : ℕ) (α : Fin (n + 1) → ι)
    (f : SchwartzMap (Fin (n + 1) → Fin 4 → ℝ) ℂ) :
    vacW (n + 1) α f = 0 := rfl

omit [Fintype ι] [DecidableEq ι] in
lemma vacW_of_one_le {n : ℕ} (hn : 1 ≤ n) (α : Fin n → ι)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    vacW n α f = 0 := by
  cases n with
  | zero => omega
  | succ m => rfl

def vacH : ∀ n : ℕ, (Fin n → ι) → (Fin n → Fin 4 → ℂ) → ℂ
  | 0, _, _ => 1
  | _ + 1, _, _ => 0

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma vacH_zero (α : Fin 0 → ι) (z : Fin 0 → Fin 4 → ℂ) :
    vacH 0 α z = 1 := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma vacH_succ (n : ℕ) (α : Fin (n + 1) → ι) (z : Fin (n + 1) → Fin 4 → ℂ) :
    vacH (n + 1) α z = 0 := rfl

omit [Fintype ι] [DecidableEq ι] in
lemma vacH_of_one_le {n : ℕ} (hn : 1 ≤ n) (α : Fin n → ι) (z : Fin n → Fin 4 → ℂ) :
    vacH n α z = 0 := by
  cases n with
  | zero => omega
  | succ m => rfl

lemma volume_fin0_eq_dirac :
    (volume : Measure (Fin 0 → Fin 4 → ℝ)) = Measure.dirac 0 := by
  rw [volume_pi, Measure.pi_of_empty]
  congr 1
  exact Subsingleton.elim _ _

@[simp]
lemma integral_fin0 (g : (Fin 0 → Fin 4 → ℝ) → ℂ) :
    (∫ x : Fin 0 → Fin 4 → ℝ, g x) = g 0 := by
  rw [volume_fin0_eq_dirac, integral_dirac]

omit [Fintype ι] [DecidableEq ι] in
noncomputable def vacTubeExtension : TubeExtension (vacW (ι := ι)) where
  H := vacH
  analytic n α := by
    cases n with
    | zero => exact analyticOn_const
    | succ m => exact analyticOn_const
  boundary n α f v _hv := by
    cases n with
    | zero =>
      have h_eq : (fun t : ℝ => ∫ x : Fin 0 → Fin 4 → ℝ,
          vacH 0 α (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ)) * f x) =
          fun _ : ℝ => vacW 0 α f := by
        ext t
        simp [vacH_zero, vacW_zero_apply]
      rw [h_eq]
      exact tendsto_const_nhds
    | succ m =>
      have h_eq : (fun t : ℝ => ∫ x : Fin (m + 1) → Fin 4 → ℝ,
          vacH (m + 1) α
            (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ)) * f x) =
          fun _ : ℝ => vacW (m + 1) α f := by
        ext t
        simp [vacH_succ]
      rw [h_eq]
      exact tendsto_const_nhds

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma vacTubeExtension_H : (vacTubeExtension (ι := ι)).H = vacH := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem schwingerFromTube_vacTubeExtension :
    schwingerFromTube (vacTubeExtension (ι := ι)) = vacS := by
  ext n α x
  cases n <;> rfl

omit [Fintype ι] [DecidableEq ι] in
theorem vacTubeTranslationInvariant :
    TubeTranslationInvariant (vacTubeExtension (ι := ι)) := by
  intro n α z a _hz
  cases n <;> rfl

theorem vacTubeComplexCovariant (R : HolomorphicLorentzRep ι) :
    ComplexCovariant R (vacTubeExtension (ι := ι)) := by
  intro n A B z _hz _hAz α
  cases n with
  | zero =>
    have hα : α = Fin.elim0 := Subsingleton.elim _ _
    subst hα
    simp [vacTubeExtension_H, vacH_zero]
  | succ m =>
    simp [vacTubeExtension_H, vacH_succ]

theorem vacTubeCovariant (R : HolomorphicLorentzRep ι) :
    TubeCovariant R (vacTubeExtension (ι := ι)) := by
  intro n A z hz hAz α
  exact vacTubeComplexCovariant R n A (sl2c_conj A) z hz hAz α

theorem vacTubeWickHermiticity {R : HolomorphicLorentzRep ι} (S : StarStructure R) :
    TubeWickHermiticity S (vacTubeExtension (ι := ι)) := by
  intro n α z _hz _hstar
  cases n with
  | zero =>
    have hα : α = Fin.elim0 := Subsingleton.elim _ _
    subst hα
    simp [vacTubeExtension_H, vacH_zero]
  | succ m =>
    simp [vacTubeExtension_H, vacH_succ]

omit [Fintype ι] [DecidableEq ι] in
theorem vacTubeWeakLocality (η : ℂ) :
    TubeWeakLocality η (vacTubeExtension (ι := ι)) := by
  intro n α z _hz
  cases n with
  | zero =>
    simp [vacTubeExtension_H, vacH_zero]
  | succ m =>
    simp [vacTubeExtension_H, vacH_succ]

omit [Fintype ι] [DecidableEq ι] in
lemma osConfig_eq_osVacuumConfig_iff (A : OSConfig ι) :
    A = osVacuumConfig ι ↔ A.1 = 0 := by
  refine ⟨fun h => h ▸ rfl, osConfig_eq_osVacuumConfig_of_fst_eq_zero⟩

open Classical in
theorem osKernel_vacS {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    (A B : OSConfig ι) :
    osKernel S vacS A B =
      if A = osVacuumConfig ι ∧ B = osVacuumConfig ι then 1 else 0 := by
  by_cases h : A = osVacuumConfig ι ∧ B = osVacuumConfig ι
  · rw [if_pos h, h.1, h.2]
    dsimp [osKernel, osVacuumConfig]
    simp
  · rw [if_neg h]
    have h_pos : 1 ≤ A.1 + B.1 := by
      by_contra hc
      have hA0 : A.1 = 0 := by omega
      have hB0 : B.1 = 0 := by omega
      exact h ⟨osConfig_eq_osVacuumConfig_of_fst_eq_zero hA0,
        osConfig_eq_osVacuumConfig_of_fst_eq_zero hB0⟩
    unfold osKernel
    refine Finset.sum_eq_zero (fun β _ => ?_)
    rw [vacS_of_one_le h_pos, mul_zero]

@[simp]
lemma osKernel_vacS_osVacuumConfig_self {R : HolomorphicLorentzRep ι} (S : StarStructure R) :
    osKernel S vacS (osVacuumConfig ι) (osVacuumConfig ι) = 1 := by
  classical
  rw [osKernel_vacS, if_pos ⟨rfl, rfl⟩]

open Classical in
lemma osKernel_vacS_osVacuumConfig_left {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    (B : OSConfig ι) :
    osKernel S vacS (osVacuumConfig ι) B =
      if B = osVacuumConfig ι then 1 else 0 := by
  rw [osKernel_vacS]
  by_cases hB : B = osVacuumConfig ι <;> simp [hB]

open Classical in
lemma osKernel_vacS_osVacuumConfig_right {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    (A : OSConfig ι) :
    osKernel S vacS A (osVacuumConfig ι) =
      if A = osVacuumConfig ι then 1 else 0 := by
  rw [osKernel_vacS]
  by_cases hA : A = osVacuumConfig ι <;> simp [hA]

lemma osKernel_vacS_factor {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    (A B : OSConfig ι) :
    osKernel S vacS A B =
      osKernel S vacS A (osVacuumConfig ι) *
        osKernel S vacS (osVacuumConfig ι) B := by
  classical
  rw [osKernel_vacS, osKernel_vacS_osVacuumConfig_right, osKernel_vacS_osVacuumConfig_left]
  by_cases hA : A = osVacuumConfig ι <;> by_cases hB : B = osVacuumConfig ι <;>
    simp [hA, hB]

theorem osPreInner_vacS {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    (Ψ Φ : OSConfig ι →₀ ℂ) :
    osPreInner S vacS Ψ Φ =
      star (Ψ (osVacuumConfig ι)) * Φ (osVacuumConfig ι) := by
  classical
  unfold osPreInner
  have h_inner : ∀ (A : OSConfig ι) (cA : ℂ),
      (Φ.sum fun B cB => star cA * cB * osKernel S vacS A B) =
        if A = osVacuumConfig ι then star cA * Φ (osVacuumConfig ι) else 0 := by
    intro A cA
    by_cases hA : A = osVacuumConfig ι
    · subst hA
      rw [if_pos rfl, Finsupp.sum]
      have h_term : ∀ B ∈ Φ.support,
          star cA * Φ B * osKernel S vacS (osVacuumConfig ι) B =
            if B = osVacuumConfig ι then star cA * Φ (osVacuumConfig ι) else 0 := by
        intro B _
        rw [osKernel_vacS_osVacuumConfig_left]
        split_ifs with hB
        · subst hB; ring
        · ring
      rw [Finset.sum_congr rfl h_term, Finset.sum_ite_eq']
      split_ifs with hmem
      · rfl
      · rw [Finsupp.notMem_support_iff.mp hmem, mul_zero]
    · rw [if_neg hA, Finsupp.sum]
      refine Finset.sum_eq_zero (fun B _ => ?_)
      rw [osKernel_vacS, if_neg (fun h => hA h.1), mul_zero]
  rw [Finsupp.sum, Finset.sum_congr rfl (fun A _ => h_inner A (Ψ A)), Finset.sum_ite_eq']
  split_ifs with hmem
  · rfl
  · rw [Finsupp.notMem_support_iff.mp hmem, star_zero, zero_mul]

theorem vacOSReflectionPositive {R : HolomorphicLorentzRep ι} (S : StarStructure R) :
    OSReflectionPositive S vacS := by
  intro Ψ
  rw [osPreInner_vacS, mul_comm]
  change (Ψ (osVacuumConfig ι) * (starRingEnd ℂ) (Ψ (osVacuumConfig ι))).re ≥ 0
  rw [Complex.mul_conj, Complex.ofReal_re]
  exact Complex.normSq_nonneg _

theorem vacOSAxioms (R : HolomorphicLorentzRep ι) (S : StarStructure R) (η : ℂ) :
    OSAxioms R S η vacS := by
  rw [← schwingerFromTube_vacTubeExtension]
  refine schwingerFromTube_osAxioms R S vacW vacTubeExtension
    vacTubeTranslationInvariant (vacTubeCovariant R)
    (vacTubeWickHermiticity S) (vacTubeWeakLocality η) ?_
  rw [schwingerFromTube_vacTubeExtension]
  exact vacOSReflectionPositive S

def vacOSData (R : HolomorphicLorentzRep ι) (S : StarStructure R) :
    OSReflectionPositiveData R S :=
  (vacOSAxioms R S 1).toReflectionPositiveData

@[simp]
lemma vacOSData_𝒮 (R : HolomorphicLorentzRep ι) (S : StarStructure R) :
    (vacOSData R S).𝒮 = vacS := rfl

omit [Fintype ι] [DecidableEq ι] in
theorem vacOSTranslationInvariant : OSTranslationInvariant (vacS (ι := ι)) := by
  intro n α x _hx a
  cases n <;> rfl

theorem vacOSTimeCluster (R : HolomorphicLorentzRep ι) (S : StarStructure R) :
    OSTimeClusterDecomposition (vacOSData R S) := by
  classical
  intro A B
  have h_const : (fun τ : ℝ =>
      osKernel S (vacOSData R S).𝒮 A
        (osConfigTimeShift (max τ 0) (le_max_right τ 0) B)) =
      fun _ : ℝ =>
        osKernel S (vacOSData R S).𝒮 A (osVacuumConfig ι) *
          osKernel S (vacOSData R S).𝒮 (osVacuumConfig ι) B := by
    ext τ
    change osKernel S vacS A (osConfigTimeShift (max τ 0) (le_max_right τ 0) B) =
      osKernel S vacS A (osVacuumConfig ι) * osKernel S vacS (osVacuumConfig ι) B
    rw [← osKernel_vacS_factor S A B, osKernel_vacS, osKernel_vacS]
    have hB : osConfigTimeShift (max τ 0) (le_max_right τ 0) B = osVacuumConfig ι ↔
        B = osVacuumConfig ι := by
      rw [osConfig_eq_osVacuumConfig_iff, osConfig_eq_osVacuumConfig_iff]
      rfl
    simp [hB]
  rw [h_const]
  exact tendsto_const_nhds

theorem vacOSSpatialClusterAlong (R : HolomorphicLorentzRep ι) (S : StarStructure R)
    (a : Fin 3 → ℝ) :
    OSSpatialClusterAlong (vacOSData R S) a := by
  classical
  intro A B
  have h_const : (fun t : ℝ =>
      osKernel S (vacOSData R S).𝒮 A (osConfigSpatialShift (t • a) B)) =
      fun _ : ℝ =>
        osKernel S (vacOSData R S).𝒮 A (osVacuumConfig ι) *
          osKernel S (vacOSData R S).𝒮 (osVacuumConfig ι) B := by
    ext t
    change osKernel S vacS A (osConfigSpatialShift (t • a) B) =
      osKernel S vacS A (osVacuumConfig ι) * osKernel S vacS (osVacuumConfig ι) B
    rw [← osKernel_vacS_factor S A B, osKernel_vacS, osKernel_vacS]
    have hB : osConfigSpatialShift (t • a) B = osVacuumConfig ι ↔
        B = osVacuumConfig ι := by
      rw [osConfig_eq_osVacuumConfig_iff, osConfig_eq_osVacuumConfig_iff]
      rfl
    simp [hB]
  rw [h_const]
  exact tendsto_const_nhds

theorem vacOSSpatialCluster (R : HolomorphicLorentzRep ι) (S : StarStructure R) :
    OSSpatialClusterDecomposition (vacOSData R S) :=
  fun a _ha => vacOSSpatialClusterAlong R S a

theorem vacOSContraction (R : HolomorphicLorentzRep ι) (S : StarStructure R) :
    OSContractionCondition (vacOSData R S) :=
  osContractionCondition_of_timeCluster (vacOSData R S)
    vacOSTranslationInvariant (vacOSTimeCluster R S)

theorem vacHilbert_eq_smul_osVacuum (R : HolomorphicLorentzRep ι) (S : StarStructure R)
    (Φ : OSHilbert (vacOSData R S)) :
    Φ = ⟪osVacuum (vacOSData R S), Φ⟫_ℂ • osVacuum (vacOSData R S) :=
  eq_smul_osVacuum_of_twoPoint_eq_zero (vacOSData R S)
    vacOSTranslationInvariant vacS_vacuumNormalized (fun _ _ _ => rfl) Φ

lemma vacHilbert_clm_eq_id_of_map_vacuum (R : HolomorphicLorentzRep ι) (S : StarStructure R)
    (L : OSHilbert (vacOSData R S) →L[ℂ] OSHilbert (vacOSData R S))
    (hL : L (osVacuum (vacOSData R S)) = osVacuum (vacOSData R S)) :
    L = ContinuousLinearMap.id ℂ (OSHilbert (vacOSData R S)) := by
  ext x
  rw [vacHilbert_eq_smul_osVacuum R S x, map_smul, hL, ContinuousLinearMap.id_apply]

@[simp]
theorem vacOSContractionSemigroup_eq_id (R : HolomorphicLorentzRep ι) (S : StarStructure R)
    (hcontr : OSContractionCondition (vacOSData R S)) (τ : ℝ) (hτ : 0 ≤ τ) :
    osContractionSemigroup (vacOSData R S) hcontr τ hτ =
      ContinuousLinearMap.id ℂ (OSHilbert (vacOSData R S)) :=
  vacHilbert_clm_eq_id_of_map_vacuum R S _
    (osContractionSemigroup_vacuum (vacOSData R S) hcontr τ hτ)

@[simp]
theorem vacOSSpatialTranslate_eq_id (R : HolomorphicLorentzRep ι) (S : StarStructure R)
    (htrans : OSTranslationInvariant (vacOSData R S).𝒮) (a : Fin 3 → ℝ) :
    osSpatialTranslate (vacOSData R S) htrans a =
      ContinuousLinearMap.id ℂ (OSHilbert (vacOSData R S)) :=
  vacHilbert_clm_eq_id_of_map_vacuum R S _
    (osSpatialTranslate_vacuum (vacOSData R S) htrans a)

def vacHolomorphicSemigroup (R : HolomorphicLorentzRep ι) (S : StarStructure R) :
    OSHolomorphicSemigroup (vacOSData R S) (vacOSContraction R S) where
  Z _ _ := ContinuousLinearMap.id ℂ (OSHilbert (vacOSData R S))
  real_eq τ hτ := (vacOSContractionSemigroup_eq_id R S (vacOSContraction R S) τ hτ).symm
  map_add _ _ _ _ := (ContinuousLinearMap.id_comp _).symm
  vacuum _ _ := rfl
  contraction _ _ _ := le_rfl
  adjoint_symm _ _ _ _ := rfl
  comm_spatial _ _ _ _ := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma minkowskiFourier_fin0 (f : SchwartzMap (Fin 0 → Fin 4 → ℝ) ℂ)
    (p : Fin 0 → Fin 4 → ℝ) :
    minkowskiFourier f p = f 0 := by
  unfold minkowskiFourier
  simp

omit [Fintype ι] [DecidableEq ι] in
lemma zero_mem_spectralRegion_zero :
    (0 : Fin 0 → Fin 4 → ℝ) ∈ spectralRegion 0 := by
  refine ⟨by simp, fun k => Fin.elim0 k, rfl⟩

omit [Fintype ι] [DecidableEq ι] in
theorem vacSpectrumCondition : SpectrumCondition (vacW (ι := ι)) := by
  intro n α f hspec
  cases n with
  | zero =>
    rw [vacW_zero_apply]
    rcases hspec with ⟨U, _hopen, hsub, hU⟩ | h0
    · have h0U : (0 : Fin 0 → Fin 4 → ℝ) ∈ U := hsub zero_mem_spectralRegion_zero
      have hf0 := hU 0 h0U
      rwa [minkowskiFourier_fin0] at hf0
    · rwa [minkowskiFourier_fin0] at h0
  | succ m =>
    exact vacW_succ_apply m α f

theorem vacPoincareCovariant (R : HolomorphicLorentzRep ι) :
    PoincareCovariant R (vacW (ι := ι)) := by
  intro n a A f f' hf α
  cases n with
  | zero =>
    have hα : α = Fin.elim0 := Subsingleton.elim _ _
    subst hα
    simp only [vacW_zero_apply, Fin.prod_univ_zero, one_mul, Fintype.sum_unique]
    have h0 := hf 0
    have h_act : (fun i : Fin 0 => poincareAct a A ((0 : Fin 0 → Fin 4 → ℝ) i)) = 0 :=
      Subsingleton.elim _ _
    rwa [h_act] at h0
  | succ m =>
    simp

omit [Fintype ι] [DecidableEq ι] in
theorem vacWeakLocality (η : ℂ) : WeakLocality η (vacW (ι := ι)) := by
  intro n α f f' _hsupp hrev
  cases n with
  | zero =>
    simp only [vacW_zero_apply, Nat.zero_mul, Nat.zero_div, pow_zero, one_mul]
    have h0 := hrev 0
    have h_eq : (fun i : Fin 0 => (0 : Fin 0 → Fin 4 → ℝ) (Fin.rev i)) = 0 :=
      Subsingleton.elim _ _
    rw [h_eq] at h0
    exact h0.symm
  | succ m =>
    simp

theorem vacPositivity {R : HolomorphicLorentzRep ι} (S : StarStructure R) :
    Positivity S (vacW (ι := ι)) := by
  intro N F G hG
  have h_outer : ∀ j ∈ Finset.range (N + 1),
      (∑ k ∈ Finset.range (N + 1),
        ∑ α : Fin j → ι, ∑ α' : Fin k → ι, ∑ β : Fin j → ι,
          (∏ i, S.C (α i) (β i)) * vacW (j + k) (Fin.append (β ∘ Fin.rev) α') (G j k α α')) =
      if j = 0 then
        star (F 0 Fin.elim0 0) * F 0 Fin.elim0 0
      else 0 := by
    intro j _hj
    by_cases hj0 : j = 0
    · subst hj0
      rw [if_pos rfl]
      have h_inner : ∀ k ∈ Finset.range (N + 1),
          (∑ α : Fin 0 → ι, ∑ α' : Fin k → ι, ∑ β : Fin 0 → ι,
            (∏ i, S.C (α i) (β i)) *
              vacW (0 + k) (Fin.append (β ∘ Fin.rev) α') (G 0 k α α')) =
          if k = 0 then star (F 0 Fin.elim0 0) * F 0 Fin.elim0 0 else 0 := by
        intro k _hk
        by_cases hk0 : k = 0
        · subst hk0
          rw [if_pos rfl]
          simp only [Nat.add_zero, Fin.prod_univ_zero, one_mul,
            Fintype.sum_unique, vacW_zero_apply]
          have hG0 := hG 0 0 Fin.elim0 Fin.elim0 0
          have h1 : (fun i : Fin 0 => (0 : Fin 0 → Fin 4 → ℝ) (Fin.castAdd 0 (Fin.rev i))) = 0 :=
            Subsingleton.elim _ _
          have h2 : (fun i : Fin 0 => (0 : Fin 0 → Fin 4 → ℝ) (Fin.natAdd 0 i)) = 0 :=
            Subsingleton.elim _ _
          have h3 : (default : Fin 0 → ι) = Fin.elim0 := Subsingleton.elim _ _
          rw [h1, h2] at hG0
          rw [h3, hG0]
          rfl
        · rw [if_neg hk0]
          have hpos : 1 ≤ 0 + k := by omega
          refine Finset.sum_eq_zero (fun α _ => Finset.sum_eq_zero (fun α' _ =>
            Finset.sum_eq_zero (fun β _ => ?_)))
          rw [vacW_of_one_le hpos, mul_zero]
      rw [Finset.sum_congr rfl h_inner, Finset.sum_ite_eq']
      simp
    · rw [if_neg hj0]
      refine Finset.sum_eq_zero (fun k _ => Finset.sum_eq_zero (fun α _ =>
        Finset.sum_eq_zero (fun α' _ => Finset.sum_eq_zero (fun β _ => ?_))))
      have hpos : 1 ≤ j + k := by omega
      rw [vacW_of_one_le hpos, mul_zero]
  rw [Finset.sum_congr rfl h_outer, Finset.sum_ite_eq']
  simp only [Finset.mem_range, Nat.zero_lt_succ, ↓reduceIte]
  rw [mul_comm]
  change (0 : ℂ) ≤ (F 0 Fin.elim0 0) * (starRingEnd ℂ) (F 0 Fin.elim0 0)
  rw [Complex.mul_conj]
  exact_mod_cast Complex.normSq_nonneg _

noncomputable def vacOSReconstructedWightman
    (R : HolomorphicLorentzRep ι) (S : StarStructure R) (η : ℂ) :
    OSReconstructedWightman R S η vacS where
  osAxioms := vacOSAxioms R S η
  contraction := vacOSContraction R S
  semigroup := vacHolomorphicSemigroup R S
  W := vacW
  E := vacTubeExtension
  schwinger_eq n α x _ := by rw [schwingerFromTube_vacTubeExtension]
  tube_covariant := vacTubeCovariant R
  tube_weakLocality := vacTubeWeakLocality η
  spectrum := vacSpectrumCondition
  poincare := vacPoincareCovariant R
  weakLocality := vacWeakLocality η
  positivity := vacPositivity S

theorem vacOSReconstructedWightman_nonempty
    (R : HolomorphicLorentzRep ι) (S : StarStructure R) (η : ℂ) :
    Nonempty (OSReconstructedWightman R S η vacS) :=
  ⟨vacOSReconstructedWightman R S η⟩

noncomputable def scalarVacuumTheory (η : ℂ) :
    ScalarOSReconstructedWightman η vacS :=
  vacOSReconstructedWightman trivialRep trivialStarStructure η

noncomputable def vectorVacuumTheory (η : ℂ) :
    VectorOSReconstructedWightman η vacS :=
  vacOSReconstructedWightman stdRep stdStarStructure η

noncomputable def diracVacuumTheory (η : ℂ) :
    DiracOSReconstructedWightman η vacS :=
  vacOSReconstructedWightman diracRep diracStarStructure η

noncomputable def spinorTensorBispinorVacuumTheory (m₁ m₂ : ℕ) (η : ℂ) :
    SpinorTensorBispinorOSReconstructedWightman m₁ m₂ η vacS :=
  vacOSReconstructedWightman
    (directSumRep (spinorTensorRep m₁ m₂) (chiralSwapRep (spinorTensorRep m₁ m₂)))
    (spinorTensorBispinorStarStructure m₁ m₂) η

noncomputable def vacHilbertLinearIsometryEquiv
    (R : HolomorphicLorentzRep ι) (S : StarStructure R) :
    OSHilbert (vacOSData R S) ≃ₗᵢ[ℂ] ℂ where
  toFun Φ := ⟪osVacuum (vacOSData R S), Φ⟫_ℂ
  map_add' Φ₁ Φ₂ := inner_add_right _ Φ₁ Φ₂
  map_smul' c Φ := by simp
  invFun c := c • osVacuum (vacOSData R S)
  left_inv Φ := (vacHilbert_eq_smul_osVacuum R S Φ).symm
  right_inv c := by
    dsimp
    rw [inner_smul_right,
        inner_osVacuum_self_of_normalized (vacOSData R S) vacS_vacuumNormalized,
        mul_one]
  norm_map' Φ := by
    dsimp
    conv_rhs => rw [vacHilbert_eq_smul_osVacuum R S Φ]
    rw [norm_smul, norm_osVacuum_of_normalized (vacOSData R S) vacS_vacuumNormalized,
        mul_one]

@[simp]
theorem vacSpinorRot_eq_id (R : HolomorphicLorentzRep ι) (S : StarStructure R)
    (η : ℂ) (U : SU2) :
    (vacOSReconstructedWightman R S η).spinorRot U =
      ContinuousLinearMap.id ℂ (vacOSReconstructedWightman R S η).Hilbert :=
  vacHilbert_clm_eq_id_of_map_vacuum R S _
    ((vacOSReconstructedWightman R S η).spinorRot_vacuum U)

@[simp]
theorem vacSpacetimeTranslate_eq_id (R : HolomorphicLorentzRep ι) (S : StarStructure R)
    (η : ℂ) (a : Fin 4 → ℝ) :
    (vacOSReconstructedWightman R S η).semigroup.spacetimeTranslate
      (vacOSReconstructedWightman R S η).osAxioms.os1_translation a =
      ContinuousLinearMap.id ℂ (vacOSReconstructedWightman R S η).Hilbert :=
  vacHilbert_clm_eq_id_of_map_vacuum R S _
    ((vacOSReconstructedWightman R S η).semigroup.spacetimeTranslate_vacuum
      (vacOSReconstructedWightman R S η).osAxioms.os1_translation a)

@[simp]
theorem vacFieldPrependLM_toOSHilbert_eq_zero
    (R : HolomorphicLorentzRep ι) (S : StarStructure R)
    (α₀ : ι) (x₀ : Fin 4 → ℝ) (hx₀ : 0 < x₀ 0)
    (Ψ : OSPreHilbertSpace (vacOSData R S)) :
    toOSHilbert (vacOSData R S) (osFieldPrependLM (vacOSData R S) α₀ x₀ hx₀ Ψ) = 0 :=
  toOSHilbert_osFieldPrependLM_eq_zero_of_twoPoint_eq_zero (vacOSData R S)
    vacOSTranslationInvariant (fun _ _ _ => rfl) α₀ x₀ hx₀ Ψ

namespace OSReconstructedWightman

variable {R : HolomorphicLorentzRep ι} {S : StarStructure R}
  {η : ℂ} {𝒮 : SchwingerFamily ι}

omit [Fintype ι] [DecidableEq ι] in
theorem schwinger_zero_eq_vacS_of_normalized
    (hnorm : OSVacuumNormalized 𝒮) (α : Fin 0 → ι) (x : Fin 0 → Fin 4 → ℝ) :
    𝒮 0 α x = vacS 0 α x := by
  have hα : α = Fin.elim0 := Subsingleton.elim _ _
  have hx : x = euclidOrderedBasePoint 0 := Subsingleton.elim _ _
  rw [hα, hx, vacS_zero]
  exact hnorm

theorem schwinger_eq_vacS_of_twoPoint_eq_zero
    (P : OSReconstructedWightman R S η 𝒮) (hnorm : OSVacuumNormalized 𝒮)
    (h2 : ∀ (β : Fin 2 → ι) (y : Fin 2 → Fin 4 → ℝ),
      y ∈ orderedEuclidN 2 → 𝒮 2 β y = 0)
    (n : ℕ) (α : Fin n → ι) {x : Fin n → Fin 4 → ℝ} (hx : x ∈ orderedEuclidN n) :
    𝒮 n α x = vacS n α x := by
  cases n with
  | zero => exact schwinger_zero_eq_vacS_of_normalized hnorm α x
  | succ m =>
    rw [vacS_succ]
    exact P.schwinger_eq_zero_of_twoPoint_eq_zero h2 (m + 1) (by omega) α hx

theorem schwinger_eq_vacS_iff_twoPoint_eq_zero
    (P : OSReconstructedWightman R S η 𝒮) (hnorm : OSVacuumNormalized 𝒮) :
    (∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → 𝒮 n α x = vacS n α x) ↔
    (∀ (β : Fin 2 → ι) (y : Fin 2 → Fin 4 → ℝ),
      y ∈ orderedEuclidN 2 → 𝒮 2 β y = 0) :=
  ⟨fun hall β y hy => hall 2 β y hy,
   fun h2 n α _x hx => P.schwinger_eq_vacS_of_twoPoint_eq_zero hnorm h2 n α hx⟩

theorem tube_H_eq_vacH_of_twoPoint_eq_zero
    (P : OSReconstructedWightman R S η 𝒮) (hnorm : OSVacuumNormalized 𝒮)
    (h2 : ∀ (β : Fin 2 → ι) (y : Fin 2 → Fin 4 → ℝ),
      y ∈ orderedEuclidN 2 → 𝒮 2 β y = 0)
    (n : ℕ) (α : Fin n → ι) (z : Fin n → Fin 4 → ℂ) (hz : z ∈ forward_tube_n n) :
    P.E.H n α z = vacH n α z := by
  refine tubeExtension_eq_of_schwingerFromTube_eq P.E vacTubeExtension ?_ n α z hz
  intro m β x hx
  rw [← P.schwinger_eq m β x hx, schwingerFromTube_vacTubeExtension]
  exact P.schwinger_eq_vacS_of_twoPoint_eq_zero hnorm h2 m β hx

theorem wightman_eq_vacW_of_twoPoint_eq_zero
    (P : OSReconstructedWightman R S η 𝒮) (hnorm : OSVacuumNormalized 𝒮)
    (h2 : ∀ (β : Fin 2 → ι) (y : Fin 2 → Fin 4 → ℝ),
      y ∈ orderedEuclidN 2 → 𝒮 2 β y = 0) :
    P.W = vacW := by
  apply wightman_eq_of_schwingerFromTube_eq_unconditional P.E vacTubeExtension
  intro n α x hx
  rw [← P.schwinger_eq n α x hx, schwingerFromTube_vacTubeExtension]
  exact P.schwinger_eq_vacS_of_twoPoint_eq_zero hnorm h2 n α hx

theorem wightman_eq_vacW_iff_twoPoint_wightman_eq_zero
    (P : OSReconstructedWightman R S η 𝒮) (hnorm : OSVacuumNormalized 𝒮)
    (hinj : TubeBoundaryInjective P.E) :
    P.W = vacW ↔
      ∀ (β : Fin 2 → ι) (f : SchwartzMap (Fin 2 → Fin 4 → ℝ) ℂ), P.W 2 β f = 0 := by
  refine ⟨fun h β f => by rw [h]; rfl, fun hW2 => ?_⟩
  exact P.wightman_eq_vacW_of_twoPoint_eq_zero hnorm
    ((P.all_nPoint_eq_zero_of_wightman_twoPoint_eq_zero hinj hW2).1 2 (by omega))

end OSReconstructedWightman

def momentS (c : ℕ → ℂ) : SchwingerFamily ι :=
  fun n _ _ => c n

def momentH (c : ℕ → ℂ) : ∀ n : ℕ, (Fin n → ι) → (Fin n → Fin 4 → ℂ) → ℂ :=
  fun n _ _ => c n

noncomputable def schwartzIntegralCLM (n : ℕ) :
    TemperedDistribution (Fin n → Fin 4 → ℝ) ℂ :=
  SchwartzMap.integralCLM ℂ (volume : Measure (Fin n → Fin 4 → ℝ))

@[simp]
lemma schwartzIntegralCLM_apply (n : ℕ) (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    schwartzIntegralCLM n f = ∫ x : Fin n → Fin 4 → ℝ, f x := rfl

noncomputable def momentW (c : ℕ → ℂ) : WightmanFamily ι :=
  fun n _ => c n • schwartzIntegralCLM n

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma momentW_apply (c : ℕ → ℂ) (n : ℕ) (α : Fin n → ι)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    momentW c n α f = c n * ∫ x : Fin n → Fin 4 → ℝ, f x := rfl

noncomputable def unitIntegralSchwartz (n : ℕ) : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ :=
  invMinkowskiFourierCLM n (vladimirov_psi_schwartz n 1 Real.zero_lt_one 0)

@[simp]
theorem integral_unitIntegralSchwartz (n : ℕ) :
    (∫ x : Fin n → Fin 4 → ℝ, unitIntegralSchwartz n x) = 1 := by
  rw [← minkowskiFourier_eval_zero_n]
  exact vladimirov_fourier_eval_zero_n n 0

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem momentW_unitIntegralSchwartz (c : ℕ → ℂ) (n : ℕ) (α : Fin n → ι) :
    momentW (ι := ι) c n α (unitIntegralSchwartz n) = c n := by
  rw [momentW_apply, integral_unitIntegralSchwartz, mul_one]

lemma integral_poincareAct_eq (n : ℕ) (a : Fin 4 → ℝ) (A : SL2C)
    (g : (Fin n → Fin 4 → ℝ) → ℂ) :
    (∫ x : Fin n → Fin 4 → ℝ, g (fun i => poincareAct a A (x i))) =
      ∫ x : Fin n → Fin 4 → ℝ, g x := by
  have h_eq : (fun x : Fin n → Fin 4 → ℝ => g (fun i => poincareAct a A (x i))) =
      fun x => g (lorentzEquiv n A x + fun _ => a) := rfl
  rw [h_eq]
  have h_mp := measurePreserving_lorentzEquiv_n n A
  have h_emb := (lorentzEquiv n A).toHomeomorph.measurableEmbedding
  rw [h_mp.integral_comp h_emb (fun y => g (y + fun _ => a))]
  exact integral_add_right_eq_self g (fun _ => a)

noncomputable def momentTubeExtension (c : ℕ → ℂ) :
    TubeExtension (momentW (ι := ι) c) where
  H := momentH c
  analytic _ _ := analyticOn_const
  boundary n α f v _hv := by
    have h_eq : (fun t : ℝ => ∫ x : Fin n → Fin 4 → ℝ,
        momentH (ι := ι) c n α
          (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ)) * f x) =
        fun _ => c n * ∫ x : Fin n → Fin 4 → ℝ, f x := by
      ext t
      dsimp [momentH]
      exact integral_const_mul (c n) f
    rw [h_eq, momentW_apply]
    exact tendsto_const_nhds

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma momentTubeExtension_H (c : ℕ → ℂ) :
    (momentTubeExtension (ι := ι) c).H = momentH c := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem schwingerFromTube_momentTubeExtension (c : ℕ → ℂ) :
    schwingerFromTube (momentTubeExtension (ι := ι) c) = momentS c := rfl

omit [Fintype ι] [DecidableEq ι] in
theorem momentTubeBoundaryInjective (c : ℕ → ℂ) :
    TubeBoundaryInjective (momentTubeExtension (ι := ι) c) := by
  intro n α hW _z _hz
  have h_unit := hW (unitIntegralSchwartz n)
  rwa [momentW_unitIntegralSchwartz] at h_unit

omit [Fintype ι] [DecidableEq ι] in
theorem momentTubeTranslationInvariant (c : ℕ → ℂ) :
    TubeTranslationInvariant (momentTubeExtension (ι := ι) c) :=
  fun _ _ _ _ _ => rfl

theorem momentTubeCovariant (c : ℕ → ℂ) :
    TubeCovariant trivialRep (momentTubeExtension (ι := Unit) c) := by
  intro n A z _hz _hAz α
  simp [momentTubeExtension_H, momentH, trivialRep, HolomorphicLorentzRep.rep_apply]

omit [Fintype ι] [DecidableEq ι] in
theorem momentTubeWeakLocality (c : ℕ → ℂ) :
    TubeWeakLocality 1 (momentTubeExtension (ι := ι) c) := by
  intro n α z _hz
  simp [momentTubeExtension_H, momentH]

lemma zero_mem_closure_forward_light_cone :
    (0 : Fin 4 → ℝ) ∈ closure forward_light_cone := by
  have h_tend : Tendsto (fun t : ℝ => fun i : Fin 4 => if i = 0 then t else 0)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : Fin 4 → ℝ)) := by
    refine tendsto_pi_nhds.mpr (fun i => ?_)
    by_cases hi : i = 0
    · subst hi
      simp only [↓reduceIte, Pi.zero_apply]
      exact tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    · simp only [if_neg hi, Pi.zero_apply]
      exact tendsto_const_nhds
  refine mem_closure_of_tendsto h_tend ?_
  refine eventually_nhdsWithin_of_forall (fun t (ht : 0 < t) => ?_)
  refine ⟨by simp [ht], ?_⟩
  rw [minkowskiInner_explicit]
  simp only [Fin.isValue, ↓reduceIte, one_ne_zero, mul_zero, sub_zero,
    Fin.reduceEq, gt_iff_lt, mul_self_pos, ne_eq]
  exact ne_of_gt ht

lemma zero_mem_spectralRegion (n : ℕ) :
    (0 : Fin n → Fin 4 → ℝ) ∈ spectralRegion n := by
  refine ⟨by simp, fun _ => ?_, rfl⟩
  simp [zero_mem_closure_forward_light_cone]

omit [Fintype ι] [DecidableEq ι] in
theorem momentSpectrumCondition (c : ℕ → ℂ) :
    SpectrumCondition (momentW (ι := ι) c) := by
  intro n α f hf
  have h0 : minkowskiFourier f 0 = 0 := by
    rcases hf with ⟨U, _hU_open, hU_sub, hU_zero⟩ | h0
    · exact hU_zero 0 (hU_sub (zero_mem_spectralRegion n))
    · exact h0
  rw [minkowskiFourier_eval_zero_n] at h0
  rw [momentW_apply, h0, mul_zero]

theorem momentPoincareCovariant (c : ℕ → ℂ) :
    PoincareCovariant trivialRep (momentW (ι := Unit) c) := by
  rw [trivialRep_covariant_iff]
  intro n a A f f' hf' α
  rw [momentW_apply, momentW_apply]
  congr 1
  have h_f : (fun x : Fin n → Fin 4 → ℝ => f x) =
      fun x => f' (fun i => poincareAct a A (x i)) := by
    ext x
    exact (hf' x).symm
  rw [h_f, integral_poincareAct_eq]

omit [Fintype ι] [DecidableEq ι] in
theorem momentWeakLocality (c : ℕ → ℂ) :
    WeakLocality 1 (momentW (ι := ι) c) := by
  intro n α f f' _hf_jost hf'
  rw [one_pow, one_mul, momentW_apply, momentW_apply]
  congr 1
  have h_f : (fun x : Fin n → Fin 4 → ℝ => f x) =
      fun x => f' (fun i => x (Fin.rev i)) := by
    ext x
    exact (hf' x).symm
  rw [h_f, integral_comp_rev]

omit [Fintype ι] [DecidableEq ι] in
theorem momentOSTranslationInvariant (c : ℕ → ℂ) :
    OSTranslationInvariant (momentS (ι := ι) c) :=
  fun _ _ _ _ _ => rfl

def osConfigLen (A : OSConfig ι) : ℕ := A.1

lemma osKernel_momentS {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    (c : ℕ → ℂ) (A B : OSConfig ι) :
    osKernel S (momentS c) A B =
      (∑ β : Fin A.1 → ι, (∏ i, S.C (A.2.1 i) (β i))) * c (A.1 + B.1) := by
  dsimp [osKernel, momentS]
  rw [Finset.sum_mul]

lemma osKernel_trivialStarStructure_momentS (c : ℕ → ℂ) (A B : OSConfig Unit) :
    osKernel trivialStarStructure (momentS c) A B = c (osConfigLen A + osConfigLen B) := by
  unfold osKernel momentS trivialStarStructure osConfigLen
  simp

theorem osBasis_eq_of_momentS {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {c : ℕ → ℂ} (D : OSReflectionPositiveData R S) (hD : D.𝒮 = momentS c)
    (A B : OSConfig ι) (hn : A.1 = B.1) (hα : HEq A.2.1 B.2.1) :
    osBasis D A = osBasis D B := by
  have h_sub : ‖osBasisPre D A - osBasisPre D B‖ = 0 := by
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ)]
    rw [inner_sub_left, inner_sub_right, inner_sub_right]
    simp only [inner_osBasisPre, hD, osKernel_momentS]
    rcases A with ⟨nA, αA, xA, hxA⟩
    rcases B with ⟨nB, αB, xB, hxB⟩
    dsimp at hn hα
    subst hn
    subst hα
    simp
  rw [← sub_eq_zero, ← norm_eq_zero]
  change ‖toOSHilbert D (osBasisPre D A) - toOSHilbert D (osBasisPre D B)‖ = 0
  rw [← map_sub, norm_toOSHilbert]
  exact h_sub

theorem momentOSContraction {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {c : ℕ → ℂ} (D : OSReflectionPositiveData R S) (hD : D.𝒮 = momentS c) :
    OSContractionCondition D := by
  intro τ hτ Ψ
  have h_inner := osPreHilbert_inner_map_eq_of_osBasisPre₂ D
    (osTimeShiftLM D τ hτ) LinearMap.id (fun A B => by
      unfold osTimeShiftLM
      rw [osLiftConfigMap_osBasisPre, osLiftConfigMap_osBasisPre, LinearMap.id_apply,
          LinearMap.id_apply, inner_osBasisPre, inner_osBasisPre, hD,
          osKernel_momentS, osKernel_momentS]
      rfl) Ψ Ψ
  have h_norm : ‖osTimeShiftLM D τ hτ Ψ‖ = ‖Ψ‖ := by
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ), h_inner]
    rfl
  exact le_of_eq h_norm

@[simp]
theorem momentOSContractionSemigroup_eq_id {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {c : ℕ → ℂ} (D : OSReflectionPositiveData R S) (hD : D.𝒮 = momentS c)
    (hcontr : OSContractionCondition D) (τ : ℝ) (hτ : 0 ≤ τ) :
    osContractionSemigroup D hcontr τ hτ = ContinuousLinearMap.id ℂ (OSHilbert D) := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih Ψ =>
    change osContractionSemigroup D hcontr τ hτ (toOSHilbert D Ψ) = toOSHilbert D Ψ
    rw [osContractionSemigroup_toOSHilbert]
    conv_lhs => rw [osPreHilbert_eq_finsupp_sum_osBasisPre D Ψ]
    conv_rhs => rw [osPreHilbert_eq_finsupp_sum_osBasisPre D Ψ]
    rw [map_finsuppSum, map_finsuppSum, map_finsuppSum]
    refine Finsupp.sum_congr (fun A _ => ?_)
    rw [LinearMap.map_smul, (toOSHilbert D).map_smul, (toOSHilbert D).map_smul]
    congr 1
    unfold osTimeShiftLM
    rw [osLiftConfigMap_osBasisPre]
    exact osBasis_eq_of_momentS D hD (osConfigTimeShift τ hτ A) A rfl HEq.rfl

def momentHolomorphicSemigroup {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {c : ℕ → ℂ} (D : OSReflectionPositiveData R S) (hD : D.𝒮 = momentS c)
    (hcontr : OSContractionCondition D) :
    OSHolomorphicSemigroup D hcontr where
  Z _ _ := ContinuousLinearMap.id ℂ (OSHilbert D)
  real_eq τ hτ := (momentOSContractionSemigroup_eq_id D hD hcontr τ hτ).symm
  map_add _ _ _ _ := (ContinuousLinearMap.id_comp _).symm
  vacuum _ _ := rfl
  contraction _ _ _ := le_rfl
  adjoint_symm _ _ _ _ := rfl
  comm_spatial _ _ _ _ := rfl

def twoModeMoment (w₁ w₂ r₁ r₂ : ℝ) (n : ℕ) : ℂ :=
  ((w₁ * r₁ ^ n + w₂ * r₂ ^ n : ℝ) : ℂ)

lemma twoModeMoment_add (w₁ w₂ r₁ r₂ : ℝ) (j k : ℕ) :
    twoModeMoment w₁ w₂ r₁ r₂ (j + k) =
      (w₁ : ℂ) * ((r₁ : ℂ) ^ j * (r₁ : ℂ) ^ k) +
      (w₂ : ℂ) * ((r₂ : ℂ) ^ j * (r₂ : ℂ) ^ k) := by
  dsimp [twoModeMoment]
  rw [pow_add, pow_add]
  push_cast
  ring

lemma sum_star_mul_pow_eq_normSq {α : Type*} (s : Finset α) (f : α → ℂ) (d : α → ℕ) (μ : ℝ) :
    (∑ a ∈ s, ∑ b ∈ s, (starRingEnd ℂ) (f a) * f b * ((μ : ℂ) ^ (d a) * (μ : ℂ) ^ (d b))) =
      ((Complex.normSq (∑ a ∈ s, (μ : ℂ) ^ (d a) * f a) : ℝ) : ℂ) := by
  have h_term : ∀ a b : α,
      (starRingEnd ℂ) (f a) * f b * ((μ : ℂ) ^ (d a) * (μ : ℂ) ^ (d b)) =
        (starRingEnd ℂ) ((μ : ℂ) ^ (d a) * f a) * ((μ : ℂ) ^ (d b) * f b) := by
    intro a b
    rw [map_mul, map_pow, Complex.conj_ofReal]
    ring
  simp_rw [h_term, ← Finset.mul_sum, ← Finset.sum_mul, ← map_sum]
  rw [mul_comm, Complex.mul_conj]

theorem twoModeTubeWickHermiticity (w₁ w₂ r₁ r₂ : ℝ) :
    TubeWickHermiticity trivialStarStructure
      (momentTubeExtension (ι := Unit) (twoModeMoment w₁ w₂ r₁ r₂)) := by
  intro n α z _hz _hstar
  simp [momentTubeExtension_H, momentH, twoModeMoment, trivialStarStructure]

theorem twoModeOSReflectionPositive {w₁ w₂ : ℝ} (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) (r₁ r₂ : ℝ) :
    OSReflectionPositive trivialStarStructure (momentS (twoModeMoment w₁ w₂ r₁ r₂)) := by
  intro Ψ
  unfold osPreInner Finsupp.sum
  simp_rw [osKernel_trivialStarStructure_momentS, twoModeMoment_add]
  have h_split : ∀ a b : OSConfig Unit,
      star (Ψ a) * Ψ b *
        ((w₁ : ℂ) * ((r₁ : ℂ) ^ osConfigLen a * (r₁ : ℂ) ^ osConfigLen b) +
         (w₂ : ℂ) * ((r₂ : ℂ) ^ osConfigLen a * (r₂ : ℂ) ^ osConfigLen b)) =
      (w₁ : ℂ) * ((starRingEnd ℂ) (Ψ a) * Ψ b *
        ((r₁ : ℂ) ^ osConfigLen a * (r₁ : ℂ) ^ osConfigLen b)) +
      (w₂ : ℂ) * ((starRingEnd ℂ) (Ψ a) * Ψ b *
        ((r₂ : ℂ) ^ osConfigLen a * (r₂ : ℂ) ^ osConfigLen b)) := by
    intro a b
    change (starRingEnd ℂ) (Ψ a) * Ψ b * _ = _
    ring
  simp_rw [h_split, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [sum_star_mul_pow_eq_normSq Ψ.support Ψ osConfigLen r₁,
      sum_star_mul_pow_eq_normSq Ψ.support Ψ osConfigLen r₂]
  have h_nonneg : 0 ≤ w₁ * Complex.normSq (∑ a ∈ Ψ.support, (r₁ : ℂ) ^ osConfigLen a * Ψ a) +
      w₂ * Complex.normSq (∑ a ∈ Ψ.support, (r₂ : ℂ) ^ osConfigLen a * Ψ a) :=
    add_nonneg (mul_nonneg hw₁ (Complex.normSq_nonneg _))
      (mul_nonneg hw₂ (Complex.normSq_nonneg _))
  exact_mod_cast h_nonneg

theorem twoModeOSAxioms {w₁ w₂ : ℝ} (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) (r₁ r₂ : ℝ) :
    OSAxioms trivialRep trivialStarStructure 1 (momentS (twoModeMoment w₁ w₂ r₁ r₂)) := by
  rw [← schwingerFromTube_momentTubeExtension]
  refine schwingerFromTube_osAxioms trivialRep trivialStarStructure
    (momentW (twoModeMoment w₁ w₂ r₁ r₂))
    (momentTubeExtension (twoModeMoment w₁ w₂ r₁ r₂))
    (momentTubeTranslationInvariant (twoModeMoment w₁ w₂ r₁ r₂))
    (momentTubeCovariant (twoModeMoment w₁ w₂ r₁ r₂))
    (twoModeTubeWickHermiticity w₁ w₂ r₁ r₂)
    (momentTubeWeakLocality (twoModeMoment w₁ w₂ r₁ r₂)) ?_
  rw [schwingerFromTube_momentTubeExtension]
  exact twoModeOSReflectionPositive hw₁ hw₂ r₁ r₂

theorem twoModePositivity {w₁ w₂ : ℝ} (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) (r₁ r₂ : ℝ) :
    Positivity trivialStarStructure (momentW (twoModeMoment w₁ w₂ r₁ r₂)) := by
  intro N F G hG
  let I : ℕ → ℂ := fun j => ∫ y : Fin j → Fin 4 → ℝ, F j default y
  have h_term : ∀ j k : ℕ,
      (∑ α : Fin j → Unit, ∑ α' : Fin k → Unit, ∑ β : Fin j → Unit,
        (∏ i, trivialStarStructure.C (α i) (β i)) *
          momentW (twoModeMoment w₁ w₂ r₁ r₂) (j + k) (Fin.append (β ∘ Fin.rev) α')
            (G j k α α')) =
      (starRingEnd ℂ) (I j) * I k * twoModeMoment w₁ w₂ r₁ r₂ (j + k) := by
    intro j k
    simp only [Fintype.sum_unique, trivialStarStructure, Matrix.one_apply_eq,
      Finset.prod_const_one, one_mul, momentW_apply]
    have hG_eq : (fun x : Fin (j + k) → Fin 4 → ℝ => G j k default default x) =
        fun x => (starRingEnd ℂ) (F j default (fun i => x (Fin.castAdd k (Fin.rev i)))) *
          F k default (fun i => x (Fin.natAdd j i)) := by
      ext x
      exact hG j k default default x
    rw [hG_eq, integral_split_rev_mul j k (fun y => (starRingEnd ℂ) (F j default y))
      (fun z => F k default z), integral_conj]
    dsimp [I]
    ring
  simp_rw [h_term, twoModeMoment_add]
  have h_split : ∀ j k : ℕ,
      (starRingEnd ℂ) (I j) * I k *
        ((w₁ : ℂ) * ((r₁ : ℂ) ^ j * (r₁ : ℂ) ^ k) +
         (w₂ : ℂ) * ((r₂ : ℂ) ^ j * (r₂ : ℂ) ^ k)) =
      (w₁ : ℂ) * ((starRingEnd ℂ) (I j) * I k * ((r₁ : ℂ) ^ j * (r₁ : ℂ) ^ k)) +
      (w₂ : ℂ) * ((starRingEnd ℂ) (I j) * I k * ((r₂ : ℂ) ^ j * (r₂ : ℂ) ^ k)) := by
    intro j k; ring
  simp_rw [h_split, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [sum_star_mul_pow_eq_normSq (Finset.range (N + 1)) I (fun n => n) r₁,
      sum_star_mul_pow_eq_normSq (Finset.range (N + 1)) I (fun n => n) r₂]
  have h_nonneg : 0 ≤ w₁ * Complex.normSq (∑ a ∈ Finset.range (N + 1), (r₁ : ℂ) ^ a * I a) +
      w₂ * Complex.normSq (∑ a ∈ Finset.range (N + 1), (r₂ : ℂ) ^ a * I a) :=
    add_nonneg (mul_nonneg hw₁ (Complex.normSq_nonneg _))
      (mul_nonneg hw₂ (Complex.normSq_nonneg _))
  exact_mod_cast h_nonneg

noncomputable def twoModeOSReconstructedWightman
    {w₁ w₂ : ℝ} (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) (r₁ r₂ : ℝ) :
    ScalarOSReconstructedWightman 1 (momentS (twoModeMoment w₁ w₂ r₁ r₂)) where
  osAxioms := twoModeOSAxioms hw₁ hw₂ r₁ r₂
  contraction := momentOSContraction (twoModeOSAxioms hw₁ hw₂ r₁ r₂).toReflectionPositiveData rfl
  semigroup := momentHolomorphicSemigroup
    (twoModeOSAxioms hw₁ hw₂ r₁ r₂).toReflectionPositiveData rfl
    (momentOSContraction (twoModeOSAxioms hw₁ hw₂ r₁ r₂).toReflectionPositiveData rfl)
  W := momentW (twoModeMoment w₁ w₂ r₁ r₂)
  E := momentTubeExtension (twoModeMoment w₁ w₂ r₁ r₂)
  schwinger_eq _ _ _ _ := rfl
  tube_covariant := momentTubeCovariant (twoModeMoment w₁ w₂ r₁ r₂)
  tube_weakLocality := momentTubeWeakLocality (twoModeMoment w₁ w₂ r₁ r₂)
  spectrum := momentSpectrumCondition (twoModeMoment w₁ w₂ r₁ r₂)
  poincare := momentPoincareCovariant (twoModeMoment w₁ w₂ r₁ r₂)
  weakLocality := momentWeakLocality (twoModeMoment w₁ w₂ r₁ r₂)
  positivity := twoModePositivity hw₁ hw₂ r₁ r₂

def coherentCoeff (r : ℝ) : ℕ → ℂ :=
  twoModeMoment 1 0 r 0

@[simp]
lemma coherentCoeff_apply (r : ℝ) (n : ℕ) :
    coherentCoeff r n = (r : ℂ) ^ n := by
  dsimp [coherentCoeff, twoModeMoment]
  push_cast
  ring

def coherentS (r : ℝ) : SchwingerFamily Unit :=
  momentS (coherentCoeff r)

noncomputable def coherentW (r : ℝ) : WightmanFamily Unit :=
  momentW (coherentCoeff r)

noncomputable def coherentOSReconstructedWightman (r : ℝ) :
    ScalarOSReconstructedWightman 1 (coherentS r) :=
  twoModeOSReconstructedWightman zero_le_one le_rfl r 0

theorem coherentOSTimeCluster (r : ℝ) :
    OSTimeClusterDecomposition (coherentOSReconstructedWightman r).osData := by
  intro A B
  have h_const : (fun τ : ℝ =>
      osKernel trivialStarStructure (coherentOSReconstructedWightman r).osData.𝒮 A
        (osConfigTimeShift (max τ 0) (le_max_right τ 0) B)) =
      fun _ : ℝ =>
        osKernel trivialStarStructure (coherentOSReconstructedWightman r).osData.𝒮 A
          (osVacuumConfig Unit) *
        osKernel trivialStarStructure (coherentOSReconstructedWightman r).osData.𝒮
          (osVacuumConfig Unit) B := by
    ext τ
    change osKernel trivialStarStructure (momentS (coherentCoeff r)) A
        (osConfigTimeShift (max τ 0) (le_max_right τ 0) B) =
      osKernel trivialStarStructure (momentS (coherentCoeff r)) A (osVacuumConfig Unit) *
        osKernel trivialStarStructure (momentS (coherentCoeff r)) (osVacuumConfig Unit) B
    rw [osKernel_trivialStarStructure_momentS, osKernel_trivialStarStructure_momentS,
        osKernel_trivialStarStructure_momentS]
    change coherentCoeff r (A.1 + B.1) = coherentCoeff r (A.1 + 0) * coherentCoeff r (0 + B.1)
    simp [coherentCoeff_apply, pow_add]
  rw [h_const]
  exact tendsto_const_nhds

theorem coherentOSSpatialCluster (r : ℝ) :
    OSSpatialClusterDecomposition (coherentOSReconstructedWightman r).osData := by
  intro a _ha A B
  have h_const : (fun t : ℝ =>
      osKernel trivialStarStructure (coherentOSReconstructedWightman r).osData.𝒮 A
        (osConfigSpatialShift (t • a) B)) =
      fun _ : ℝ =>
        osKernel trivialStarStructure (coherentOSReconstructedWightman r).osData.𝒮 A
          (osVacuumConfig Unit) *
        osKernel trivialStarStructure (coherentOSReconstructedWightman r).osData.𝒮
          (osVacuumConfig Unit) B := by
    ext t
    change osKernel trivialStarStructure (momentS (coherentCoeff r)) A
        (osConfigSpatialShift (t • a) B) =
      osKernel trivialStarStructure (momentS (coherentCoeff r)) A (osVacuumConfig Unit) *
        osKernel trivialStarStructure (momentS (coherentCoeff r)) (osVacuumConfig Unit) B
    rw [osKernel_trivialStarStructure_momentS, osKernel_trivialStarStructure_momentS,
        osKernel_trivialStarStructure_momentS]
    change coherentCoeff r (A.1 + B.1) = coherentCoeff r (A.1 + 0) * coherentCoeff r (0 + B.1)
    simp [coherentCoeff_apply, pow_add]
  rw [h_const]
  exact tendsto_const_nhds

noncomputable def z2FreeCoeff : ℕ → ℂ :=
  twoModeMoment (1 / 2) (1 / 2) 1 (-1)

noncomputable def z2FreeS : SchwingerFamily Unit :=
  momentS z2FreeCoeff

noncomputable def z2FreeW : WightmanFamily Unit :=
  momentW z2FreeCoeff

noncomputable def z2FreeTubeExtension : TubeExtension z2FreeW :=
  momentTubeExtension z2FreeCoeff

noncomputable def z2FreeOSReconstructedWightman :
    ScalarOSReconstructedWightman 1 z2FreeS :=
  twoModeOSReconstructedWightman (by positivity) (by positivity) 1 (-1)

noncomputable def z2FreeOSData : OSReflectionPositiveData trivialRep trivialStarStructure :=
  z2FreeOSReconstructedWightman.osData

lemma z2FreeCoeff_eq_ite (n : ℕ) :
    z2FreeCoeff n = if n % 2 = 0 then 1 else 0 := by
  dsimp [z2FreeCoeff, twoModeMoment]
  rw [one_pow]
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · have hmod : (2 * k) % 2 = 0 := by omega
    rw [if_pos hmod, pow_mul, neg_one_sq, one_pow]
    push_cast
    ring
  · have hmod : (2 * k + 1) % 2 ≠ 0 := by omega
    rw [if_neg hmod, pow_add, pow_mul, neg_one_sq, one_pow, pow_one]
    push_cast
    ring

@[simp] theorem z2FreeCoeff_zero : z2FreeCoeff 0 = 1 := by rw [z2FreeCoeff_eq_ite]; rfl
@[simp] theorem z2FreeCoeff_one : z2FreeCoeff 1 = 0 := by rw [z2FreeCoeff_eq_ite]; rfl
@[simp] theorem z2FreeCoeff_two : z2FreeCoeff 2 = 1 := by rw [z2FreeCoeff_eq_ite]; rfl
@[simp] theorem z2FreeCoeff_three : z2FreeCoeff 3 = 0 := by rw [z2FreeCoeff_eq_ite]; rfl
@[simp] theorem z2FreeCoeff_four : z2FreeCoeff 4 = 1 := by rw [z2FreeCoeff_eq_ite]; rfl

theorem z2FreeS_vacuumNormalized : OSVacuumNormalized z2FreeS := by
  unfold OSVacuumNormalized z2FreeS momentS
  exact z2FreeCoeff_zero

@[simp]
theorem z2FreeS_one_eq_zero (α : Fin 1 → Unit) (x : Fin 1 → Fin 4 → ℝ) :
    z2FreeS 1 α x = 0 := z2FreeCoeff_one

@[simp]
theorem z2FreeS_two_eq_one (α : Fin 2 → Unit) (x : Fin 2 → Fin 4 → ℝ) :
    z2FreeS 2 α x = 1 := z2FreeCoeff_two

@[simp]
theorem z2FreeW_one_eq_zero (α : Fin 1 → Unit) (f : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) :
    z2FreeW 1 α f = 0 := by
  change z2FreeCoeff 1 * ∫ x, f x = 0
  rw [z2FreeCoeff_one, zero_mul]

@[simp]
theorem z2FreeW_two_unitIntegralSchwartz (α : Fin 2 → Unit) :
    z2FreeW 2 α (unitIntegralSchwartz 2) = 1 := by
  change momentW z2FreeCoeff 2 α (unitIntegralSchwartz 2) = 1
  rw [momentW_unitIntegralSchwartz, z2FreeCoeff_two]

theorem z2FreeW_twoPoint_nondegenerate :
    ∃ (α : Fin 2 → Unit) (f : SchwartzMap (Fin 2 → Fin 4 → ℝ) ℂ), z2FreeW 2 α f ≠ 0 :=
  ⟨default, unitIntegralSchwartz 2, by rw [z2FreeW_two_unitIntegralSchwartz]; exact one_ne_zero⟩

theorem z2FreeW_ne_vacW : z2FreeW ≠ vacW := by
  intro h
  have h2 : z2FreeW 2 (default : Fin 2 → Unit) (unitIntegralSchwartz 2) =
      vacW 2 (default : Fin 2 → Unit) (unitIntegralSchwartz 2) := by rw [h]
  rw [z2FreeW_two_unitIntegralSchwartz, vacW_succ_apply] at h2
  exact one_ne_zero h2

theorem z2FreeS_ne_vacS : z2FreeS ≠ vacS := by
  intro h
  have h2 : z2FreeS 2 (default : Fin 2 → Unit) (euclidOrderedBasePoint 2) =
      vacS 2 (default : Fin 2 → Unit) (euclidOrderedBasePoint 2) := by rw [h]
  rw [z2FreeS_two_eq_one, vacS_succ] at h2
  exact one_ne_zero h2

theorem z2Free_spin_statistics_unconditional {η : ℂ} {𝒮 : SchwingerFamily Unit}
    (P : ScalarOSReconstructedWightman η 𝒮) (hW : P.W = z2FreeW) :
    η = 1 := by
  refine scalar_os_spin_statistics_unconditional P ?_
  rw [hW]
  exact z2FreeW_twoPoint_nondegenerate

theorem coherent_spin_statistics_unconditional {η : ℂ} {r : ℝ} (hr : r ≠ 0)
    {𝒮 : SchwingerFamily Unit} (P : ScalarOSReconstructedWightman η 𝒮)
    (hW : P.W = coherentW r) :
    η = 1 := by
  refine scalar_os_spin_statistics_unconditional P ?_
  rw [hW]
  refine ⟨default, unitIntegralSchwartz 2, ?_⟩
  change momentW (coherentCoeff r) 2 default (unitIntegralSchwartz 2) ≠ 0
  rw [momentW_unitIntegralSchwartz, coherentCoeff_apply]
  exact pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr hr)

noncomputable def osBaseConfig (n : ℕ) : OSConfig Unit :=
  ⟨n, (default, ⟨euclidOrderedBasePoint n, euclidOrderedBasePoint_mem_posOrderedEuclidN n⟩)⟩

noncomputable def z2FreeOneParticle : OSHilbert z2FreeOSData :=
  osBasis z2FreeOSData (osBaseConfig 1)

theorem osBasis_z2FreeOSData_eq_of_mod_two_eq (A B : OSConfig Unit)
    (h : A.1 % 2 = B.1 % 2) :
    osBasis z2FreeOSData A = osBasis z2FreeOSData B := by
  have h_sub : ‖osBasisPre z2FreeOSData A - osBasisPre z2FreeOSData B‖ = 0 := by
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ)]
    rw [inner_sub_left, inner_sub_right, inner_sub_right]
    simp only [inner_osBasisPre]
    change Real.sqrt (RCLike.re
      (osKernel trivialStarStructure z2FreeS A A -
       osKernel trivialStarStructure z2FreeS A B -
       (osKernel trivialStarStructure z2FreeS B A -
        osKernel trivialStarStructure z2FreeS B B))) = 0
    simp only [z2FreeS, osKernel_trivialStarStructure_momentS, osConfigLen, z2FreeCoeff_eq_ite]
    have hAA : (A.1 + A.1) % 2 = 0 := by omega
    have hAB : (A.1 + B.1) % 2 = 0 := by omega
    have hBA : (B.1 + A.1) % 2 = 0 := by omega
    have hBB : (B.1 + B.1) % 2 = 0 := by omega
    rw [if_pos hAA, if_pos hAB, if_pos hBA, if_pos hBB]
    simp
  rw [← sub_eq_zero, ← norm_eq_zero]
  change ‖toOSHilbert z2FreeOSData (osBasisPre z2FreeOSData A) -
    toOSHilbert z2FreeOSData (osBasisPre z2FreeOSData B)‖ = 0
  rw [← map_sub, norm_toOSHilbert]
  exact h_sub

theorem osBasis_z2FreeOSData_eq_ite (A : OSConfig Unit) :
    osBasis z2FreeOSData A =
      if A.1 % 2 = 0 then osVacuum z2FreeOSData else z2FreeOneParticle := by
  by_cases h : A.1 % 2 = 0
  · rw [if_pos h]
    exact osBasis_z2FreeOSData_eq_of_mod_two_eq A (osVacuumConfig Unit) h
  · rw [if_neg h]
    have h1 : A.1 % 2 = (osBaseConfig 1).1 % 2 := by
      change A.1 % 2 = 1 % 2
      omega
    exact osBasis_z2FreeOSData_eq_of_mod_two_eq A (osBaseConfig 1) h1

@[simp]
theorem inner_osVacuum_z2FreeOSData_self :
    ⟪osVacuum z2FreeOSData, osVacuum z2FreeOSData⟫_ℂ = 1 := by
  rw [inner_osVacuum_self]
  exact z2FreeCoeff_zero

@[simp]
theorem norm_osVacuum_z2FreeOSData :
    ‖osVacuum z2FreeOSData‖ = 1 := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), inner_osVacuum_z2FreeOSData_self]
  simp

@[simp]
theorem inner_osVacuum_z2FreeOneParticle :
    ⟪osVacuum z2FreeOSData, z2FreeOneParticle⟫_ℂ = 0 := by
  dsimp [z2FreeOneParticle]
  rw [inner_osVacuum_osBasis]
  exact z2FreeCoeff_one

@[simp]
theorem inner_z2FreeOneParticle_osVacuum :
    ⟪z2FreeOneParticle, osVacuum z2FreeOSData⟫_ℂ = 0 := by
  rw [← inner_conj_symm, inner_osVacuum_z2FreeOneParticle, map_zero]

@[simp]
theorem inner_z2FreeOneParticle_self :
    ⟪z2FreeOneParticle, z2FreeOneParticle⟫_ℂ = 1 := by
  dsimp [z2FreeOneParticle]
  rw [inner_osBasis]
  change osKernel trivialStarStructure z2FreeS (osBaseConfig 1) (osBaseConfig 1) = 1
  rw [z2FreeS, osKernel_trivialStarStructure_momentS]
  exact z2FreeCoeff_two

@[simp]
theorem norm_z2FreeOneParticle : ‖z2FreeOneParticle‖ = 1 := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), inner_z2FreeOneParticle_self]
  simp

theorem z2FreeOneParticle_ne_zero : z2FreeOneParticle ≠ 0 := by
  intro h
  have := norm_z2FreeOneParticle
  rw [h, norm_zero] at this
  exact zero_ne_one this

theorem z2FreeHilbert_eq_vacuum_add_oneParticle (Φ : OSHilbert z2FreeOSData) :
    Φ = ⟪osVacuum z2FreeOSData, Φ⟫_ℂ • osVacuum z2FreeOSData +
        ⟪z2FreeOneParticle, Φ⟫_ℂ • z2FreeOneParticle := by
  have h_basis : ∀ A : OSConfig Unit,
      osBasis z2FreeOSData A =
        ⟪osVacuum z2FreeOSData, osBasis z2FreeOSData A⟫_ℂ • osVacuum z2FreeOSData +
        ⟪z2FreeOneParticle, osBasis z2FreeOSData A⟫_ℂ • z2FreeOneParticle := by
    intro A
    rw [osBasis_z2FreeOSData_eq_ite A]
    split_ifs with h
    · rw [inner_osVacuum_z2FreeOSData_self, inner_z2FreeOneParticle_osVacuum,
        one_smul, zero_smul, add_zero]
    · rw [inner_osVacuum_z2FreeOneParticle, inner_z2FreeOneParticle_self,
        zero_smul, one_smul, zero_add]
  induction Φ using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih Ψ =>
    change toOSHilbert z2FreeOSData Ψ =
      ⟪osVacuum z2FreeOSData, toOSHilbert z2FreeOSData Ψ⟫_ℂ • osVacuum z2FreeOSData +
      ⟪z2FreeOneParticle, toOSHilbert z2FreeOSData Ψ⟫_ℂ • z2FreeOneParticle
    have h_expand : toOSHilbert z2FreeOSData Ψ =
        ∑ A ∈ Ψ.toFinsupp.support, Ψ.toFinsupp A • osBasis z2FreeOSData A := by
      conv_lhs => rw [osPreHilbert_eq_finsupp_sum_osBasisPre z2FreeOSData Ψ]
      rw [map_finsuppSum]
      unfold Finsupp.sum
      refine Finset.sum_congr rfl (fun A _ => (toOSHilbert z2FreeOSData).map_smul _ _)
    rw [h_expand, inner_sum, inner_sum, Finset.sum_smul, Finset.sum_smul,
        ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun A _ => ?_)
    rw [inner_smul_right, inner_smul_right, mul_smul, mul_smul, ← smul_add, ← h_basis A]

noncomputable def orthogonalTwoLinearIsometryEquiv
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (e₀ e₁ : H)
    (h00 : ⟪e₀, e₀⟫_ℂ = 1) (h01 : ⟪e₀, e₁⟫_ℂ = 0)
    (h10 : ⟪e₁, e₀⟫_ℂ = 0) (h11 : ⟪e₁, e₁⟫_ℂ = 1)
    (hn0 : ‖e₀‖ = 1) (hn1 : ‖e₁‖ = 1)
    (h_span : ∀ Φ : H, Φ = ⟪e₀, Φ⟫_ℂ • e₀ + ⟪e₁, Φ⟫_ℂ • e₁) :
    H ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin 2) where
  toFun Φ := WithLp.toLp 2 ![⟪e₀, Φ⟫_ℂ, ⟪e₁, Φ⟫_ℂ]
  map_add' x y := by
    ext i
    fin_cases i <;> simp
  map_smul' c x := by
    ext i
    fin_cases i <;> simp
  invFun v := v.ofLp 0 • e₀ + v.ofLp 1 • e₁
  left_inv Φ := (h_span Φ).symm
  right_inv v := by
    ext i
    fin_cases i
    · simp [h01, hn0]
    · simp [h10, hn1]
  norm_map' Φ := by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_two]
    change Real.sqrt (‖⟪e₀, Φ⟫_ℂ‖ ^ 2 + ‖⟪e₁, Φ⟫_ℂ‖ ^ 2) = ‖Φ‖
    conv_rhs => rw [h_span Φ, norm_eq_sqrt_re_inner (𝕜 := ℂ)]
    congr 1
    rw [inner_add_left, inner_add_right, inner_add_right,
        inner_smul_left, inner_smul_right, inner_smul_left, inner_smul_right,
        inner_smul_left, inner_smul_right, inner_smul_left, inner_smul_right,
        h00, h01, h10, h11]
    have h_re : ∀ z : ℂ, RCLike.re (starRingEnd ℂ z * (z * 1)) = ‖z‖ ^ 2 := by
      intro z
      rw [mul_one, mul_comm, Complex.mul_conj]
      exact Complex.normSq_eq_norm_sq z
    simp only [mul_zero, add_zero, zero_add, map_add, h_re]

noncomputable def z2FreeHilbertLinearIsometryEquiv :
    OSHilbert z2FreeOSData ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin 2) :=
  orthogonalTwoLinearIsometryEquiv
    (osVacuum z2FreeOSData) z2FreeOneParticle
    inner_osVacuum_z2FreeOSData_self inner_osVacuum_z2FreeOneParticle
    inner_z2FreeOneParticle_osVacuum inner_z2FreeOneParticle_self
    norm_osVacuum_z2FreeOSData norm_z2FreeOneParticle
    z2FreeHilbert_eq_vacuum_add_oneParticle

theorem norm_schwinger_twoPoint_le_sqrt_osKernel_fourPoint
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S)
    (α : Fin 2 → ι) (y : posOrderedEuclidN 2) :
    ‖D.𝒮 2 α y.val‖ ≤
      ‖osVacuumPre D‖ *
        Real.sqrt (RCLike.re (osKernel S D.𝒮 ⟨2, (α, y)⟩ ⟨2, (α, y)⟩)) := by
  let A₂ : OSConfig ι := ⟨2, (α, y)⟩
  have h_eq : D.𝒮 2 α y.val = ⟪osVacuumPre D, osBasisPre D A₂⟫_ℂ :=
    (inner_osVacuumPre_osBasisPre D A₂).symm
  rw [h_eq]
  have h_cs := osPreHilbert_cauchy_schwarz D (osVacuumPre D) (osBasisPre D A₂)
  have h_norm : ‖osBasisPre D A₂‖ =
      Real.sqrt (RCLike.re (osKernel S D.𝒮 A₂ A₂)) := by
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), inner_osBasisPre]
  rwa [h_norm] at h_cs

theorem schwinger_twoPoint_posOrdered_eq_zero_of_fourPoint_eq_zero
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S)
    (h4 : ∀ (γ : Fin 4 → ι) (z : Fin 4 → Fin 4 → ℝ),
      z ∈ orderedEuclidN 4 → D.𝒮 4 γ z = 0)
    (α : Fin 2 → ι) {y : Fin 2 → Fin 4 → ℝ} (hy : y ∈ posOrderedEuclidN 2) :
    D.𝒮 2 α y = 0 := by
  let A₂ : OSConfig ι := ⟨2, (α, ⟨y, hy⟩)⟩
  have hK : osKernel S D.𝒮 A₂ A₂ = 0 :=
    osKernel_eq_zero_of_schwinger_eq_zero S D.𝒮 A₂ A₂ h4
  have h_orth : ⟪osBasisPre D A₂, osVacuumPre D⟫_ℂ = 0 :=
    inner_osBasisPre_eq_zero_of_osKernel_self_eq_zero D hK (osVacuumPre D)
  rw [inner_osBasisPre_osVacuumPre] at h_orth
  exact star_eq_zero.mp h_orth

theorem schwinger_twoPoint_eq_zero_of_fourPoint_eq_zero
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (htrans : OSTranslationInvariant D.𝒮)
    (h4 : ∀ (γ : Fin 4 → ι) (z : Fin 4 → Fin 4 → ℝ),
      z ∈ orderedEuclidN 4 → D.𝒮 4 γ z = 0)
    (α : Fin 2 → ι) {x : Fin 2 → Fin 4 → ℝ} (hx : x ∈ orderedEuclidN 2) :
    D.𝒮 2 α x = 0 :=
  schwinger_eq_zero_of_posOrderedEuclidN_eq_zero htrans 2 α
    (fun _y hy => schwinger_twoPoint_posOrdered_eq_zero_of_fourPoint_eq_zero D h4 α hy) hx

theorem exists_fourPoint_ne_zero_of_twoPoint_ne_zero
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (htrans : OSTranslationInvariant D.𝒮)
    (h2 : ∃ (α : Fin 2 → ι) (x : Fin 2 → Fin 4 → ℝ),
      x ∈ orderedEuclidN 2 ∧ D.𝒮 2 α x ≠ 0) :
    ∃ (γ : Fin 4 → ι) (z : Fin 4 → Fin 4 → ℝ),
      z ∈ orderedEuclidN 4 ∧ D.𝒮 4 γ z ≠ 0 := by
  by_contra h4
  push Not at h4
  rcases h2 with ⟨α, x, hx, hne⟩
  exact hne (schwinger_twoPoint_eq_zero_of_fourPoint_eq_zero D htrans h4 α hx)

theorem schwinger_all_nPoint_eq_zero_iff_fourPoint_eq_zero
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (htrans : OSTranslationInvariant D.𝒮) :
    (∀ (n : ℕ), 1 ≤ n → ∀ (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → D.𝒮 n α x = 0) ↔
    (∀ (γ : Fin 4 → ι) (z : Fin 4 → Fin 4 → ℝ),
      z ∈ orderedEuclidN 4 → D.𝒮 4 γ z = 0) := by
  refine ⟨fun hall γ z hz => hall 4 (by omega) γ z hz, fun h4 n hn α x hx => ?_⟩
  exact schwinger_eq_zero_of_twoPoint_eq_zero D htrans
    (fun β _y hy => schwinger_twoPoint_eq_zero_of_fourPoint_eq_zero D htrans h4 β hy)
    n hn α hx

noncomputable def vacSpectralDecomposition
    (R : HolomorphicLorentzRep ι) (S : StarStructure R) :
    OSSpectralDecomposition (vacOSData R S) (vacOSContraction R S) 1 where
  E _ := 0
  energy_nonneg _ := le_rfl
  P _ := rankOneProjCLM (osVacuum (vacOSData R S))
  proj_selfAdjoint _ x y := rankOneProjCLM_selfAdjoint _ x y
  proj_mul j k := by
    fin_cases j
    fin_cases k
    rw [if_pos rfl]
    exact rankOneProjCLM_comp_self
      (inner_osVacuum_self_of_normalized (vacOSData R S) vacS_vacuumNormalized)
  sum_proj x := by
    rw [Fin.sum_univ_one, rankOneProjCLM_apply]
    exact (vacHilbert_eq_smul_osVacuum R S x).symm
  semigroup_eq τ hτ x := by
    rw [vacOSContractionSemigroup_eq_id R S (vacOSContraction R S) τ hτ,
        ContinuousLinearMap.id_apply, Fin.sum_univ_one, laplaceExp_zero_left,
        one_smul, rankOneProjCLM_apply]
    exact vacHilbert_eq_smul_osVacuum R S x
  vacuum_eq z := by
    rw [Fin.sum_univ_one, laplaceExp_zero_left, one_smul, rankOneProjCLM_apply,
        inner_osVacuum_self_of_normalized (vacOSData R S) vacS_vacuumNormalized, one_smul]
  comm_spatial htrans a _ := by
    rw [vacOSSpatialTranslate_eq_id R S htrans a, ContinuousLinearMap.id_comp,
        ContinuousLinearMap.comp_id]

noncomputable def vacSpectralHolomorphicSemigroup
    (R : HolomorphicLorentzRep ι) (S : StarStructure R) :
    OSHolomorphicSemigroup (vacOSData R S) (vacOSContraction R S) :=
  (vacSpectralDecomposition R S).toOSHolomorphicSemigroup

noncomputable def vacEuclideanTubeBridge
    (R : HolomorphicLorentzRep ι) (S : StarStructure R) (η : ℂ) :
    OSEuclideanTubeBridge R S η vacS :=
  osEuclideanTubeBridgeOfTubeExtension R S η vacS vacW vacTubeExtension
    (fun n α x _ => by rw [schwingerFromTube_vacTubeExtension])
    (vacTubeCovariant R) (vacTubeWeakLocality η)
    vacSpectrumCondition (vacPoincareCovariant R) (vacWeakLocality η) (vacPositivity S)

noncomputable def vacReconstructedWightmanOfTimeCluster
    (R : HolomorphicLorentzRep ι) (S : StarStructure R) (η : ℂ) :
    OSReconstructedWightman R S η vacS :=
  osReconstructedWightmanOfTimeCluster R S η vacS
    (vacOSAxioms R S η) (vacOSTimeCluster R S)
    (vacSpectralHolomorphicSemigroup R S)
    (vacEuclideanTubeBridge R S η)

@[simp]
theorem momentOSSpatialTranslate_eq_id {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {c : ℕ → ℂ} (D : OSReflectionPositiveData R S) (hD : D.𝒮 = momentS c)
    (htrans : OSTranslationInvariant D.𝒮) (a : Fin 3 → ℝ) :
    osSpatialTranslate D htrans a = ContinuousLinearMap.id ℂ (OSHilbert D) := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih Ψ =>
    change osSpatialTranslate D htrans a (toOSHilbert D Ψ) = toOSHilbert D Ψ
    rw [osSpatialTranslate_toOSHilbert]
    conv_lhs => rw [osPreHilbert_eq_finsupp_sum_osBasisPre D Ψ]
    conv_rhs => rw [osPreHilbert_eq_finsupp_sum_osBasisPre D Ψ]
    rw [map_finsuppSum, map_finsuppSum, map_finsuppSum]
    refine Finsupp.sum_congr (fun A _ => ?_)
    rw [LinearMap.map_smul, (toOSHilbert D).map_smul, (toOSHilbert D).map_smul]
    congr 1
    unfold osSpatialTranslateLM
    rw [osLiftConfigMap_osBasisPre]
    exact osBasis_eq_of_momentS D hD (osConfigSpatialShift a A) A rfl HEq.rfl

theorem z2FreeOSContraction : OSContractionCondition z2FreeOSData :=
  momentOSContraction z2FreeOSData rfl

@[simp]
theorem z2FreeOSContractionSemigroup_eq_id (τ : ℝ) (hτ : 0 ≤ τ) :
    osContractionSemigroup z2FreeOSData z2FreeOSContraction τ hτ =
      ContinuousLinearMap.id ℂ (OSHilbert z2FreeOSData) :=
  momentOSContractionSemigroup_eq_id z2FreeOSData rfl z2FreeOSContraction τ hτ

@[simp]
theorem z2FreeOSSpatialTranslate_eq_id (htrans : OSTranslationInvariant z2FreeOSData.𝒮)
    (a : Fin 3 → ℝ) :
    osSpatialTranslate z2FreeOSData htrans a =
      ContinuousLinearMap.id ℂ (OSHilbert z2FreeOSData) :=
  momentOSSpatialTranslate_eq_id z2FreeOSData rfl htrans a

noncomputable def z2FreeSpectralDecomposition :
    OSSpectralDecomposition z2FreeOSData z2FreeOSContraction 2 where
  E _ := 0
  energy_nonneg _ := le_rfl
  P i :=
    if i = 0 then
      rankOneProjCLM (osVacuum z2FreeOSData)
    else
      rankOneProjCLM z2FreeOneParticle
  proj_selfAdjoint i x y := by
    fin_cases i <;> exact rankOneProjCLM_selfAdjoint _ x y
  proj_mul j k := by
    fin_cases j <;> fin_cases k
    · simp only [Fin.isValue, ↓reduceIte]
      exact rankOneProjCLM_comp_self inner_osVacuum_z2FreeOSData_self
    · simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, zero_ne_one, ↓reduceIte, one_ne_zero]
      exact rankOneProjCLM_comp_eq_zero_of_orth inner_osVacuum_z2FreeOneParticle
    · simp only [Fin.isValue, Fin.mk_one, one_ne_zero, ↓reduceIte, Fin.zero_eta]
      exact rankOneProjCLM_comp_eq_zero_of_orth inner_z2FreeOneParticle_osVacuum
    · simp only [Fin.isValue, Fin.mk_one, one_ne_zero, ↓reduceIte]
      exact rankOneProjCLM_comp_self inner_z2FreeOneParticle_self
  sum_proj x := by
    rw [Fin.sum_univ_two]
    have h10 : (1 : Fin 2) ≠ 0 := by decide
    rw [if_pos rfl, if_neg h10, rankOneProjCLM_apply, rankOneProjCLM_apply]
    exact (z2FreeHilbert_eq_vacuum_add_oneParticle x).symm
  semigroup_eq τ hτ x := by
    rw [z2FreeOSContractionSemigroup_eq_id τ hτ, ContinuousLinearMap.id_apply,
        Fin.sum_univ_two]
    have h10 : (1 : Fin 2) ≠ 0 := by decide
    rw [laplaceExp_zero_left, one_smul, one_smul, if_pos rfl, if_neg h10,
        rankOneProjCLM_apply, rankOneProjCLM_apply]
    exact z2FreeHilbert_eq_vacuum_add_oneParticle x
  vacuum_eq z := by
    rw [Fin.sum_univ_two]
    have h10 : (1 : Fin 2) ≠ 0 := by decide
    rw [laplaceExp_zero_left, one_smul, one_smul, if_pos rfl, if_neg h10,
        rankOneProjCLM_apply, rankOneProjCLM_apply,
        inner_osVacuum_z2FreeOSData_self, inner_z2FreeOneParticle_osVacuum,
        one_smul, zero_smul, add_zero]
  comm_spatial htrans a i := by
    rw [z2FreeOSSpatialTranslate_eq_id htrans a, ContinuousLinearMap.id_comp,
        ContinuousLinearMap.comp_id]

noncomputable def z2FreeSpectralHolomorphicSemigroup :
    OSHolomorphicSemigroup z2FreeOSData z2FreeOSContraction :=
  z2FreeSpectralDecomposition.toOSHolomorphicSemigroup

noncomputable def twoModeEuclideanTubeBridge
    {w₁ w₂ : ℝ} (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂) (r₁ r₂ : ℝ) :
    OSEuclideanTubeBridge trivialRep trivialStarStructure 1
      (momentS (twoModeMoment w₁ w₂ r₁ r₂)) :=
  osEuclideanTubeBridgeOfTubeExtension trivialRep trivialStarStructure 1
    (momentS (twoModeMoment w₁ w₂ r₁ r₂))
    (momentW (twoModeMoment w₁ w₂ r₁ r₂))
    (momentTubeExtension (twoModeMoment w₁ w₂ r₁ r₂))
    (fun _ _ _ _ => rfl)
    (momentTubeCovariant (twoModeMoment w₁ w₂ r₁ r₂))
    (momentTubeWeakLocality (twoModeMoment w₁ w₂ r₁ r₂))
    (momentSpectrumCondition (twoModeMoment w₁ w₂ r₁ r₂))
    (momentPoincareCovariant (twoModeMoment w₁ w₂ r₁ r₂))
    (momentWeakLocality (twoModeMoment w₁ w₂ r₁ r₂))
    (twoModePositivity hw₁ hw₂ r₁ r₂)

noncomputable def z2FreeEuclideanTubeBridge :
    OSEuclideanTubeBridge trivialRep trivialStarStructure 1 z2FreeS :=
  twoModeEuclideanTubeBridge (by positivity) (by positivity) 1 (-1)

theorem z2FreeOSDiagonalKernelBounded :
    OSDiagonalKernelBounded trivialStarStructure z2FreeS := by
  intro A
  refine ⟨1, fun τ hτ => ?_⟩
  change ‖osKernel trivialStarStructure (momentS z2FreeCoeff)
    (osConfigTimeShift τ hτ A) (osConfigTimeShift τ hτ A)‖ ≤ 1
  rw [osKernel_trivialStarStructure_momentS, osConfigLen, z2FreeCoeff_eq_ite]
  have h_even : ((osConfigTimeShift τ hτ A).1 + (osConfigTimeShift τ hτ A).1) % 2 = 0 := by omega
  rw [if_pos h_even]
  simp

noncomputable def z2FreeReconstructedWightmanOfDiagonalBounded :
    ScalarOSReconstructedWightman 1 z2FreeS :=
  osReconstructedWightmanOfDiagonalBounded trivialRep trivialStarStructure 1 z2FreeS
    z2FreeOSReconstructedWightman.osAxioms
    z2FreeOSDiagonalKernelBounded
    z2FreeSpectralHolomorphicSemigroup
    z2FreeEuclideanTubeBridge

noncomputable def discreteKallenLehmannTube
    (N : ℕ) (w E : Fin N → ℝ) (z : Fin 2 → Fin 4 → ℂ) : ℂ :=
  ∑ a : Fin N, (w a : ℂ) * spectralTwoPointTube (E a) z

noncomputable def discreteKallenLehmannEuclid
    (N : ℕ) (w E : Fin N → ℝ) (x : Fin 2 → Fin 4 → ℝ) : ℂ :=
  ∑ a : Fin N, (w a : ℂ) * euclidSpectralTwoPoint (E a) x

@[simp]
theorem discreteKallenLehmannTube_wickEmbedN
    (N : ℕ) (w E : Fin N → ℝ) (x : Fin 2 → Fin 4 → ℝ) :
    discreteKallenLehmannTube N w E (wickEmbedN 2 x) =
      discreteKallenLehmannEuclid N w E x := by
  unfold discreteKallenLehmannTube discreteKallenLehmannEuclid
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [spectralTwoPointTube_wickEmbedN_eq_euclidSpectralTwoPoint]

theorem differentiable_discreteKallenLehmannTube (N : ℕ) (w E : Fin N → ℝ) :
    Differentiable ℂ (discreteKallenLehmannTube N w E) := by
  unfold discreteKallenLehmannTube
  have h_term : ∀ a : Fin N,
      Differentiable ℂ (fun z => (w a : ℂ) * spectralTwoPointTube (E a) z) :=
    fun a => (differentiable_const (w a : ℂ)).mul (differentiable_spectralTwoPointTube (E a))
  fun_prop

theorem analyticOn_discreteKallenLehmannTube
    (N : ℕ) (w E : Fin N → ℝ) (s : Set (Fin 2 → Fin 4 → ℂ)) :
    AnalyticOn ℂ (discreteKallenLehmannTube N w E) s :=
  AnalyticOnNhd.analyticOn (fun z _ => by
    unfold discreteKallenLehmannTube
    refine analyticAt_finset_sum_normed Finset.univ (fun a _ => ?_)
    exact analyticAt_const.mul (analyticAt_spectralTwoPointTube (E a) z))

@[simp]
theorem discreteKallenLehmannTube_add_const
    (N : ℕ) (w E : Fin N → ℝ) (z : Fin 2 → Fin 4 → ℂ) (a : Fin 4 → ℂ) :
    discreteKallenLehmannTube N w E (fun k => z k + a) =
      discreteKallenLehmannTube N w E z := by
  unfold discreteKallenLehmannTube
  refine Finset.sum_congr rfl (fun idx _ => ?_)
  rw [spectralTwoPointTube_add_const]

theorem discreteKallenLehmannEuclid_sesquilinear_eq
    (N : ℕ) (w E : Fin N → ℝ) (m : ℕ) (c : Fin m → ℂ) (x : Fin m → Fin 1 → Fin 4 → ℝ) :
    (∑ j : Fin m, ∑ k : Fin m,
      star (c j) * c k *
        discreteKallenLehmannEuclid N w E (osConcatPoint 1 1 (x j) (x k))) =
      ∑ a : Fin N, (w a : ℂ) *
        (‖∑ k : Fin m, c k * laplaceExp (E a) (x k 0 0 : ℂ)‖ ^ 2 : ℂ) := by
  unfold discreteKallenLehmannEuclid
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext j
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.sum_comm]
  have h_pull : ∀ j k : Fin m,
      star (c j) * c k * ((w a : ℂ) *
        euclidSpectralTwoPoint (E a) (osConcatPoint 1 1 (x j) (x k))) =
      (w a : ℂ) * (star (c j) * c k *
        euclidSpectralTwoPoint (E a) (osConcatPoint 1 1 (x j) (x k))) := by
    intro j k
    ring
  simp_rw [h_pull, ← Finset.mul_sum]
  rw [euclidSpectralTwoPoint_sesquilinear_eq_norm_sq]

theorem discreteKallenLehmannEuclid_reflectionPositive
    {N : ℕ} {w : Fin N → ℝ} (hw : ∀ a : Fin N, 0 ≤ w a) (E : Fin N → ℝ)
    (m : ℕ) (c : Fin m → ℂ) (x : Fin m → Fin 1 → Fin 4 → ℝ) :
    0 ≤ RCLike.re (∑ j : Fin m, ∑ k : Fin m,
      star (c j) * c k *
        discreteKallenLehmannEuclid N w E (osConcatPoint 1 1 (x j) (x k))) := by
  rw [discreteKallenLehmannEuclid_sesquilinear_eq, map_sum]
  refine Finset.sum_nonneg (fun a _ => ?_)
  have h_re :
      RCLike.re ((w a : ℂ) *
        (‖∑ k : Fin m, c k * laplaceExp (E a) (x k 0 0 : ℂ)‖ ^ 2 : ℂ)) =
        w a * ‖∑ k : Fin m, c k * laplaceExp (E a) (x k 0 0 : ℂ)‖ ^ 2 := by
    change ((w a : ℂ) *
      ((‖∑ k : Fin m, c k * laplaceExp (E a) (x k 0 0 : ℂ)‖ : ℂ) ^ 2)).re = _
    rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [h_re]
  exact mul_nonneg (hw a) (sq_nonneg _)

theorem tendsto_discreteKallenLehmannEuclid_timeShift_atTop_zero
    {N : ℕ} (w : Fin N → ℝ) {E : Fin N → ℝ} (hE : ∀ a : Fin N, 0 < E a)
    (x y : Fin 1 → Fin 4 → ℝ) :
    Tendsto
      (fun τ : ℝ =>
        discreteKallenLehmannEuclid N w E
          (osConcatPoint 1 1 x (fun i => y i + euclidTimeVec τ)))
      atTop (𝓝 0) := by
  unfold discreteKallenLehmannEuclid
  have h_zero : (0 : ℂ) = ∑ _a : Fin N, (0 : ℂ) := by simp
  rw [h_zero]
  refine tendsto_finsetSum Finset.univ (fun a _ => ?_)
  simpa using (tendsto_euclidSpectralTwoPoint_timeShift_atTop_zero (hE a) x y).const_mul (w a : ℂ)

def weylEpsilon (α : Fin 2 → Fin 2) : ℂ :=
  if α 0 = 0 ∧ α 1 = 1 then 1
  else if α 0 = 1 ∧ α 1 = 0 then -1
  else 0

@[simp]
lemma weylEpsilon_zero_zero : weylEpsilon ![0, 0] = 0 := by simp [weylEpsilon]

@[simp]
lemma weylEpsilon_zero_one : weylEpsilon ![0, 1] = 1 := by simp [weylEpsilon]

@[simp]
lemma weylEpsilon_one_zero : weylEpsilon ![1, 0] = -1 := by simp [weylEpsilon]

@[simp]
lemma weylEpsilon_one_one : weylEpsilon ![1, 1] = 0 := by simp [weylEpsilon]

@[simp]
theorem weylEpsilon_comp_rev (α : Fin 2 → Fin 2) :
    weylEpsilon (α ∘ Fin.rev) = -weylEpsilon α := by
  rw [finTwo_eq_vecCons α, finTwo_comp_rev_vecCons]
  generalize α 0 = a
  generalize α 1 = b
  fin_cases a <;> fin_cases b <;>
    simp [weylEpsilon_zero_zero, weylEpsilon_zero_one,
          weylEpsilon_one_zero, weylEpsilon_one_one]

theorem sum_matrix_mul_weylEpsilon (M : Matrix (Fin 2) (Fin 2) ℂ) (α : Fin 2 → Fin 2) :
    (∑ β : Fin 2 → Fin 2, (∏ i : Fin 2, M (α i) (β i)) * weylEpsilon β) =
      M.det * weylEpsilon α := by
  rw [sum_fin_two_fun, Fin.sum_univ_two]
  simp only [Fin.sum_univ_two, Fin.prod_univ_two, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_one,
    weylEpsilon_zero_zero, weylEpsilon_zero_one,
    weylEpsilon_one_zero, weylEpsilon_one_one, Matrix.det_fin_two]
  rw [finTwo_eq_vecCons α]
  generalize α 0 = a
  generalize α 1 = b
  fin_cases a <;> fin_cases b <;>
    simp [weylEpsilon_zero_zero, weylEpsilon_zero_one,
          weylEpsilon_one_zero, weylEpsilon_one_one] <;>
    ring

@[simp]
theorem sum_leftWeylRep_mul_weylEpsilon (p : SL2C × SL2C) (α : Fin 2 → Fin 2) :
    (∑ β : Fin 2 → Fin 2,
      (∏ i : Fin 2, leftWeylRep.σ p (α i) (β i)) * weylEpsilon β) =
      weylEpsilon α := by
  change (∑ β : Fin 2 → Fin 2, (∏ i : Fin 2, p.1.1 (α i) (β i)) * weylEpsilon β) =
    weylEpsilon α
  rw [sum_matrix_mul_weylEpsilon p.1.1 α, p.1.2, one_mul]

def weylFermionConst : ∀ n : ℕ, (Fin n → Fin 2) → ℂ
  | 0, _ => 1
  | 2, α => weylEpsilon α
  | _, _ => 0

@[simp]
lemma weylFermionConst_zero (α : Fin 0 → Fin 2) : weylFermionConst 0 α = 1 := rfl

@[simp]
lemma weylFermionConst_one (α : Fin 1 → Fin 2) : weylFermionConst 1 α = 0 := rfl

@[simp]
lemma weylFermionConst_two (α : Fin 2 → Fin 2) : weylFermionConst 2 α = weylEpsilon α := rfl

@[simp]
lemma weylFermionConst_add_three (m : ℕ) (α : Fin (m + 3) → Fin 2) :
    weylFermionConst (m + 3) α = 0 := rfl

theorem sum_leftWeylRep_mul_weylFermionConst (n : ℕ) (p : SL2C × SL2C) (α : Fin n → Fin 2) :
    (∑ β : Fin n → Fin 2,
      (∏ i : Fin n, leftWeylRep.σ p (α i) (β i)) * weylFermionConst n β) =
      weylFermionConst n α := by
  match n with
  | 0 =>
    have hα : α = Fin.elim0 := Subsingleton.elim _ _
    subst hα
    simp [weylFermionConst]
  | 1 =>
    simp [weylFermionConst]
  | 2 =>
    exact sum_leftWeylRep_mul_weylEpsilon p α
  | m + 3 =>
    simp [weylFermionConst]

theorem weylFermionConst_eq_neg_one_pow_mul_rev (n : ℕ) (α : Fin n → Fin 2) :
    weylFermionConst n α =
      ((-1 : ℂ) ^ (n * (n - 1) / 2)) * weylFermionConst n (α ∘ Fin.rev) := by
  match n with
  | 0 =>
    simp [weylFermionConst]
  | 1 =>
    simp [weylFermionConst]
  | 2 =>
    rw [two_mul_two_sub_one_div_two, pow_one]
    change weylEpsilon α = (-1 : ℂ) * weylEpsilon (α ∘ Fin.rev)
    rw [weylEpsilon_comp_rev]
    ring
  | m + 3 =>
    simp [weylFermionConst]

def weylFermionS : SchwingerFamily (Fin 2) :=
  fun n α _ => weylFermionConst n α

def weylFermionH : ∀ n : ℕ, (Fin n → Fin 2) → (Fin n → Fin 4 → ℂ) → ℂ :=
  fun n α _ => weylFermionConst n α

noncomputable def weylFermionW : WightmanFamily (Fin 2) :=
  fun n α => weylFermionConst n α • schwartzIntegralCLM n

@[simp]
lemma weylFermionW_apply (n : ℕ) (α : Fin n → Fin 2)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    weylFermionW n α f = weylFermionConst n α * ∫ x : Fin n → Fin 4 → ℝ, f x := rfl

@[simp]
theorem weylFermionW_unitIntegralSchwartz (n : ℕ) (α : Fin n → Fin 2) :
    weylFermionW n α (unitIntegralSchwartz n) = weylFermionConst n α := by
  rw [weylFermionW_apply, integral_unitIntegralSchwartz, mul_one]

@[simp]
theorem weylFermionW_two_zero_one :
    weylFermionW 2 ![0, 1] (unitIntegralSchwartz 2) = 1 := by
  rw [weylFermionW_unitIntegralSchwartz, weylFermionConst_two, weylEpsilon_zero_one]

theorem weylFermionW_twoPoint_nondegenerate :
    ∃ (α : Fin 2 → Fin 2) (f : SchwartzMap (Fin 2 → Fin 4 → ℝ) ℂ),
      weylFermionW 2 α f ≠ 0 :=
  ⟨![0, 1], unitIntegralSchwartz 2, by rw [weylFermionW_two_zero_one]; exact one_ne_zero⟩

noncomputable def weylFermionTubeExtension : TubeExtension weylFermionW where
  H := weylFermionH
  analytic _ _ := analyticOn_const
  boundary n α f v _hv := by
    have h_eq : (fun t : ℝ => ∫ x : Fin n → Fin 4 → ℝ,
        weylFermionH n α
          (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ)) * f x) =
        fun _ => weylFermionConst n α * ∫ x : Fin n → Fin 4 → ℝ, f x := by
      ext t
      dsimp [weylFermionH]
      exact integral_const_mul (weylFermionConst n α) f
    rw [h_eq, weylFermionW_apply]
    exact tendsto_const_nhds

@[simp]
lemma weylFermionTubeExtension_H : weylFermionTubeExtension.H = weylFermionH := rfl

@[simp]
theorem schwingerFromTube_weylFermionTubeExtension :
    schwingerFromTube weylFermionTubeExtension = weylFermionS := rfl

theorem weylFermionTubeBoundaryInjective :
    TubeBoundaryInjective weylFermionTubeExtension := by
  intro n α hW _z _hz
  have h_unit := hW (unitIntegralSchwartz n)
  rwa [weylFermionW_unitIntegralSchwartz] at h_unit

theorem weylFermionTubeTranslationInvariant :
    TubeTranslationInvariant weylFermionTubeExtension :=
  fun _ _ _ _ _ => rfl

theorem weylFermionTubeCovariant :
    TubeCovariant leftWeylRep weylFermionTubeExtension := by
  intro n A z _hz _hAz α
  dsimp [weylFermionTubeExtension_H, weylFermionH, HolomorphicLorentzRep.rep_apply]
  exact (sum_leftWeylRep_mul_weylFermionConst n (A, sl2c_conj A) α).symm

theorem weylFermionTubeWeakLocality :
    TubeWeakLocality (-1) weylFermionTubeExtension := by
  intro n α z _hz
  dsimp [weylFermionTubeExtension_H, weylFermionH]
  exact weylFermionConst_eq_neg_one_pow_mul_rev n α

theorem weylFermionSpectrumCondition :
    SpectrumCondition weylFermionW := by
  intro n α f hf
  have h0 : minkowskiFourier f 0 = 0 := by
    rcases hf with ⟨U, _hU_open, hU_sub, hU_zero⟩ | h0
    · exact hU_zero 0 (hU_sub (zero_mem_spectralRegion n))
    · exact h0
  rw [minkowskiFourier_eval_zero_n] at h0
  rw [weylFermionW_apply, h0, mul_zero]

theorem weylFermionPoincareCovariant :
    PoincareCovariant leftWeylRep weylFermionW := by
  intro n a A f f' hf' α
  have h_int : (∫ x : Fin n → Fin 4 → ℝ, f x) = ∫ x : Fin n → Fin 4 → ℝ, f' x := by
    have h_f : (fun x : Fin n → Fin 4 → ℝ => f x) =
        fun x => f' (fun i => poincareAct a A (x i)) := by
      ext x
      exact (hf' x).symm
    rw [h_f, integral_poincareAct_eq]
  have h_sum : ∀ β : Fin n → Fin 2,
      (∏ i : Fin n, leftWeylRep.rep A (α i) (β i)) * weylFermionW n β f =
        ((∏ i : Fin n, leftWeylRep.σ (A, sl2c_conj A) (α i) (β i)) *
          weylFermionConst n β) * ∫ x : Fin n → Fin 4 → ℝ, f' x := by
    intro β
    rw [weylFermionW_apply, h_int, HolomorphicLorentzRep.rep_apply, mul_assoc]
  simp_rw [h_sum, ← Finset.sum_mul]
  rw [weylFermionW_apply, sum_leftWeylRep_mul_weylFermionConst n (A, sl2c_conj A) α]

theorem weylFermionWeakLocality :
    WeakLocality (-1) weylFermionW := by
  intro n α f f' _hf_jost hf'
  rw [weylFermionW_apply, weylFermionW_apply]
  have h_f : (fun x : Fin n → Fin 4 → ℝ => f x) =
      fun x => f' (fun i => x (Fin.rev i)) := by
    ext x
    exact (hf' x).symm
  rw [h_f, integral_comp_rev, ← mul_assoc]
  congr 1
  exact weylFermionConst_eq_neg_one_pow_mul_rev n α

theorem weylFermion_spin_statistics_unconditional
    {η : ℂ} (hloc : WeakLocality η weylFermionW) :
    η = -1 :=
  leftWeyl_wightman_spin_statistics_unconditional weylFermionW
    weylFermionSpectrumCondition weylFermionPoincareCovariant hloc
    weylFermionW_twoPoint_nondegenerate

theorem not_weylFermion_bosonic_weakLocality :
    ¬ WeakLocality 1 weylFermionW := by
  intro hbos
  have h := weylFermion_spin_statistics_unconditional hbos
  norm_num at h

noncomputable def multiPointKallenLehmannTube
    (n N : ℕ) (w : Fin N → ℝ) (E : Fin N → Fin (n - 1) → ℝ)
    (z : Fin n → Fin 4 → ℂ) : ℂ :=
  ∑ a : Fin N, (w a : ℂ) * spectralMultiPointTube n (E a) z

noncomputable def multiPointKallenLehmannEuclid
    (n N : ℕ) (w : Fin N → ℝ) (E : Fin N → Fin (n - 1) → ℝ)
    (x : Fin n → Fin 4 → ℝ) : ℂ :=
  ∑ a : Fin N, (w a : ℂ) * euclidSpectralMultiPoint n (E a) x

@[simp]
theorem multiPointKallenLehmannTube_wickEmbedN
    (n N : ℕ) (w : Fin N → ℝ) (E : Fin N → Fin (n - 1) → ℝ)
    (x : Fin n → Fin 4 → ℝ) :
    multiPointKallenLehmannTube n N w E (wickEmbedN n x) =
      multiPointKallenLehmannEuclid n N w E x := by
  unfold multiPointKallenLehmannTube multiPointKallenLehmannEuclid
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [spectralMultiPointTube_wickEmbedN]

theorem differentiable_multiPointKallenLehmannTube
    (n N : ℕ) (w : Fin N → ℝ) (E : Fin N → Fin (n - 1) → ℝ) :
    Differentiable ℂ (multiPointKallenLehmannTube n N w E) := by
  unfold multiPointKallenLehmannTube
  have h_term : ∀ a : Fin N,
      Differentiable ℂ (fun z => (w a : ℂ) * spectralMultiPointTube n (E a) z) :=
    fun a => (differentiable_const (w a : ℂ)).mul
      (differentiable_spectralMultiPointTube n (E a))
  fun_prop

theorem analyticOn_multiPointKallenLehmannTube
    (n N : ℕ) (w : Fin N → ℝ) (E : Fin N → Fin (n - 1) → ℝ)
    (s : Set (Fin n → Fin 4 → ℂ)) :
    AnalyticOn ℂ (multiPointKallenLehmannTube n N w E) s :=
  AnalyticOnNhd.analyticOn (fun z _ => by
    unfold multiPointKallenLehmannTube
    refine analyticAt_finset_sum_normed Finset.univ (fun a _ => ?_)
    exact analyticAt_const.mul (analyticAt_spectralMultiPointTube n (E a) z))

@[simp]
theorem multiPointKallenLehmannTube_add_const
    (n N : ℕ) (w : Fin N → ℝ) (E : Fin N → Fin (n - 1) → ℝ)
    (z : Fin n → Fin 4 → ℂ) (a : Fin 4 → ℂ) :
    multiPointKallenLehmannTube n N w E (fun k => z k + a) =
      multiPointKallenLehmannTube n N w E z := by
  unfold multiPointKallenLehmannTube
  refine Finset.sum_congr rfl (fun idx _ => ?_)
  rw [spectralMultiPointTube_add_const]

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem vladimirov_H_zero_momentW (c : ℕ → ℂ) (n : ℕ) (α : Fin n → ι) :
    vladimirov_H (momentW (ι := ι) c) n α 0 = c n := by
  have h := W_n_eq_vladimirov_H_zero_mul_integral
    (momentSpectrumCondition (ι := ι) c) n α (unitIntegralSchwartz n)
  rw [momentW_unitIntegralSchwartz, integral_unitIntegralSchwartz, mul_one] at h
  exact h.symm

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem vladimirovSchwinger_momentW (c : ℕ → ℂ) :
    vladimirovSchwinger (momentW (ι := ι) c) = momentS (ι := ι) c := by
  ext n α x
  rw [vladimirovSchwinger_eq_zero_eval (momentSpectrumCondition (ι := ι) c),
      vladimirov_H_zero_momentW]
  rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem vladimirovSchwinger_vacW :
    vladimirovSchwinger (vacW (ι := ι)) = vacS (ι := ι) := by
  ext n α x
  rw [vladimirovSchwinger_eq_zero_eval (vacSpectrumCondition (ι := ι))]
  have h := W_n_eq_vladimirov_H_zero_mul_integral
    (vacSpectrumCondition (ι := ι)) n α (unitIntegralSchwartz n)
  rw [integral_unitIntegralSchwartz, mul_one] at h
  rw [← h]
  cases n with
  | zero =>
    rw [vacW_zero_apply, ← integral_fin0 (unitIntegralSchwartz 0), vacS_zero]
    exact integral_unitIntegralSchwartz 0
  | succ m =>
    simp [vacS_succ]

theorem vac_wightmanSesquilinear_eq_inner_osWavepacketVector
    (R : HolomorphicLorentzRep ι) (S : StarStructure R) (N : ℕ)
    (F F' : ∀ j : ℕ, (Fin j → ι) → SchwartzMap (Fin j → Fin 4 → ℝ) ℂ)
    (G : ∀ j k : ℕ, (Fin j → ι) → (Fin k → ι) →
      SchwartzMap (Fin (j + k) → Fin 4 → ℝ) ℂ)
    (hG : ∀ j k α α' (x : Fin (j + k) → Fin 4 → ℝ),
      G j k α α' x =
        (starRingEnd ℂ) (F j α (fun i => x (Fin.castAdd k (Fin.rev i)))) *
          F' k α' (fun i => x (Fin.natAdd j i))) :
    (∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
      ∑ α : Fin j → ι, ∑ α' : Fin k → ι, ∑ β : Fin j → ι,
        (∏ i : Fin j, S.C (α i) (β i)) *
          vacW (j + k) (Fin.append (β ∘ Fin.rev) α') (G j k α α')) =
      ⟪osWavepacketVector (vacOSData R S) N F,
       osWavepacketVector (vacOSData R S) N F'⟫_ℂ :=
  wightmanSesquilinear_eq_inner_osWavepacketVector
    (vacOSData R S) vacSpectrumCondition vladimirovSchwinger_vacW.symm N F F' G hG

theorem z2Free_wightmanSesquilinear_eq_inner_osWavepacketVector
    (N : ℕ)
    (F F' : ∀ j : ℕ, (Fin j → Unit) → SchwartzMap (Fin j → Fin 4 → ℝ) ℂ)
    (G : ∀ j k : ℕ, (Fin j → Unit) → (Fin k → Unit) →
      SchwartzMap (Fin (j + k) → Fin 4 → ℝ) ℂ)
    (hG : ∀ j k α α' (x : Fin (j + k) → Fin 4 → ℝ),
      G j k α α' x =
        (starRingEnd ℂ) (F j α (fun i => x (Fin.castAdd k (Fin.rev i)))) *
          F' k α' (fun i => x (Fin.natAdd j i))) :
    (∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
      ∑ α : Fin j → Unit, ∑ α' : Fin k → Unit, ∑ β : Fin j → Unit,
        (∏ i : Fin j, trivialStarStructure.C (α i) (β i)) *
          z2FreeW (j + k) (Fin.append (β ∘ Fin.rev) α') (G j k α α')) =
      ⟪osWavepacketVector z2FreeOSData N F,
       osWavepacketVector z2FreeOSData N F'⟫_ℂ :=
  wightmanSesquilinear_eq_inner_osWavepacketVector
    z2FreeOSData (momentSpectrumCondition z2FreeCoeff)
    (vladimirovSchwinger_momentW z2FreeCoeff).symm N F F' G hG

theorem z2Free_wightmanSesquilinear_diag_eq_norm_sq_osWavepacketVector
    (N : ℕ)
    (F : ∀ j : ℕ, (Fin j → Unit) → SchwartzMap (Fin j → Fin 4 → ℝ) ℂ)
    (G : ∀ j k : ℕ, (Fin j → Unit) → (Fin k → Unit) →
      SchwartzMap (Fin (j + k) → Fin 4 → ℝ) ℂ)
    (hG : ∀ j k α α' (x : Fin (j + k) → Fin 4 → ℝ),
      G j k α α' x =
        (starRingEnd ℂ) (F j α (fun i => x (Fin.castAdd k (Fin.rev i)))) *
          F k α' (fun i => x (Fin.natAdd j i))) :
    (∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
      ∑ α : Fin j → Unit, ∑ α' : Fin k → Unit, ∑ β : Fin j → Unit,
        (∏ i : Fin j, trivialStarStructure.C (α i) (β i)) *
          z2FreeW (j + k) (Fin.append (β ∘ Fin.rev) α') (G j k α α')) =
      (‖osWavepacketVector z2FreeOSData N F‖ ^ 2 : ℂ) :=
  wightmanSesquilinear_diag_eq_norm_sq_osWavepacketVector
    z2FreeOSData (momentSpectrumCondition z2FreeCoeff)
    (vladimirovSchwinger_momentW z2FreeCoeff).symm N F G hG

@[simp]
theorem sum_rightWeylRep_mul_weylEpsilon (p : SL2C × SL2C) (α : Fin 2 → Fin 2) :
    (∑ β : Fin 2 → Fin 2,
      (∏ i : Fin 2, rightWeylRep.σ p (α i) (β i)) * weylEpsilon β) =
      weylEpsilon α := by
  change (∑ β : Fin 2 → Fin 2, (∏ i : Fin 2, p.2.1 (α i) (β i)) * weylEpsilon β) =
    weylEpsilon α
  rw [sum_matrix_mul_weylEpsilon p.2.1 α, p.2.2, one_mul]

@[simp]
theorem star_weylEpsilon (α : Fin 2 → Fin 2) :
    star (weylEpsilon α) = weylEpsilon α := by
  rw [finTwo_eq_vecCons α]
  generalize α 0 = a
  generalize α 1 = b
  fin_cases a <;> fin_cases b <;>
    simp [weylEpsilon_zero_zero, weylEpsilon_zero_one,
          weylEpsilon_one_zero, weylEpsilon_one_one]

noncomputable def diracEpsilon (α : Fin 2 → Fin 2 ⊕ Fin 2) : ℂ :=
  match α 0, α 1 with
  | Sum.inl a, Sum.inl b => Complex.I * weylEpsilon ![a, b]
  | Sum.inr a, Sum.inr b => Complex.I * weylEpsilon ![a, b]
  | _, _ => 0

@[simp]
lemma diracEpsilon_inl_inl (a b : Fin 2) :
    diracEpsilon ![Sum.inl a, Sum.inl b] = Complex.I * weylEpsilon ![a, b] := rfl

@[simp]
lemma diracEpsilon_inr_inr (a b : Fin 2) :
    diracEpsilon ![Sum.inr a, Sum.inr b] = Complex.I * weylEpsilon ![a, b] := rfl

@[simp]
lemma diracEpsilon_inl_inr (a b : Fin 2) :
    diracEpsilon ![Sum.inl a, Sum.inr b] = 0 := rfl

@[simp]
lemma diracEpsilon_inr_inl (a b : Fin 2) :
    diracEpsilon ![Sum.inr a, Sum.inl b] = 0 := rfl

@[simp]
lemma diracEpsilon_comp_inl (γ : Fin 2 → Fin 2) :
    diracEpsilon (Sum.inl ∘ γ) = Complex.I * weylEpsilon γ := by
  change diracEpsilon ![Sum.inl (γ 0), Sum.inl (γ 1)] = Complex.I * weylEpsilon γ
  rw [diracEpsilon_inl_inl, ← finTwo_eq_vecCons γ]

@[simp]
lemma diracEpsilon_comp_inr (γ : Fin 2 → Fin 2) :
    diracEpsilon (Sum.inr ∘ γ) = Complex.I * weylEpsilon γ := by
  change diracEpsilon ![Sum.inr (γ 0), Sum.inr (γ 1)] = Complex.I * weylEpsilon γ
  rw [diracEpsilon_inr_inr, ← finTwo_eq_vecCons γ]

@[simp]
theorem diracEpsilon_comp_rev (α : Fin 2 → Fin 2 ⊕ Fin 2) :
    diracEpsilon (α ∘ Fin.rev) = -diracEpsilon α := by
  rw [finTwo_eq_vecCons α, finTwo_comp_rev_vecCons]
  rcases α 0 with a | a <;> rcases α 1 with b | b
  · rw [diracEpsilon_inl_inl, diracEpsilon_inl_inl]
    have hrev := weylEpsilon_comp_rev ![a, b]
    rw [finTwo_comp_rev_vecCons] at hrev
    rw [hrev]
    ring
  · simp
  · simp
  · rw [diracEpsilon_inr_inr, diracEpsilon_inr_inr]
    have hrev := weylEpsilon_comp_rev ![a, b]
    rw [finTwo_comp_rev_vecCons] at hrev
    rw [hrev]
    ring

@[simp]
theorem diracEpsilon_comp_swap (α : Fin 2 → Fin 2 ⊕ Fin 2) :
    diracEpsilon (Sum.swap ∘ α) = diracEpsilon α := by
  rw [finTwo_eq_vecCons α]
  rcases α 0 with a | a <;> rcases α 1 with b | b <;> rfl

theorem star_diracEpsilon (α : Fin 2 → Fin 2 ⊕ Fin 2) :
    star (diracEpsilon α) = diracEpsilon (Sum.swap ∘ α ∘ Fin.rev) := by
  rw [diracEpsilon_comp_swap, diracEpsilon_comp_rev, finTwo_eq_vecCons α]
  rcases α 0 with a | a <;> rcases α 1 with b | b
  · rw [diracEpsilon_inl_inl, star_mul', Complex.star_def, Complex.conj_I,
        ← Complex.star_def, star_weylEpsilon]
    ring
  · simp
  · simp
  · rw [diracEpsilon_inr_inr, star_mul', Complex.star_def, Complex.conj_I,
        ← Complex.star_def, star_weylEpsilon]
    ring

@[simp]
theorem sum_diracRep_mul_diracEpsilon (p : SL2C × SL2C) (α : Fin 2 → Fin 2 ⊕ Fin 2) :
    (∑ β : Fin 2 → Fin 2 ⊕ Fin 2,
      (∏ i : Fin 2, diracRep.σ p (α i) (β i)) * diracEpsilon β) =
      diracEpsilon α := by
  rw [finTwo_eq_vecCons α]
  rcases α 0 with a | a <;> rcases α 1 with b | b
  · have h_inl : (![Sum.inl a, Sum.inl b] : Fin 2 → Fin 2 ⊕ Fin 2) =
        Sum.inl ∘ (![a, b] : Fin 2 → Fin 2) := by
      ext i
      fin_cases i <;> rfl
    rw [h_inl]
    have h_sum := sum_directSumRep_inl_two leftWeylRep rightWeylRep p.1 p.2
      diracEpsilon ![a, b]
    change (∑ β : Fin 2 → Fin 2 ⊕ Fin 2,
      (∏ i : Fin 2, (directSumRep leftWeylRep rightWeylRep).σ (p.1, p.2)
        (Sum.inl (![a, b] i)) (β i)) * diracEpsilon β) = _
    rw [h_sum]
    simp_rw [diracEpsilon_comp_inl, ← mul_assoc, mul_comm _ Complex.I, mul_assoc]
    rw [← Finset.mul_sum, sum_leftWeylRep_mul_weylEpsilon p ![a, b] ]
  · rw [diracEpsilon_inl_inr]
    refine Finset.sum_eq_zero (fun β _ => ?_)
    rw [Fin.prod_univ_two, finTwo_eq_vecCons β]
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
    rcases β 0 with x | x <;> rcases β 1 with y | y
    · have h0 : diracRep.σ p (Sum.inr b) (Sum.inl y) = 0 := rfl
      rw [h0, mul_zero, zero_mul]
    · rw [diracEpsilon_inl_inr, mul_zero]
    · have h0 : diracRep.σ p (Sum.inl a) (Sum.inr x) = 0 := rfl
      rw [h0, zero_mul, zero_mul]
    · have h0 : diracRep.σ p (Sum.inl a) (Sum.inr x) = 0 := rfl
      rw [h0, zero_mul, zero_mul]
  · rw [diracEpsilon_inr_inl]
    refine Finset.sum_eq_zero (fun β _ => ?_)
    rw [Fin.prod_univ_two, finTwo_eq_vecCons β]
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
    rcases β 0 with x | x <;> rcases β 1 with y | y
    · have h0 : diracRep.σ p (Sum.inr a) (Sum.inl x) = 0 := rfl
      rw [h0, zero_mul, zero_mul]
    · have h0 : diracRep.σ p (Sum.inr a) (Sum.inl x) = 0 := rfl
      rw [h0, zero_mul, zero_mul]
    · rw [diracEpsilon_inr_inl, mul_zero]
    · have h0 : diracRep.σ p (Sum.inl b) (Sum.inr y) = 0 := rfl
      rw [h0, mul_zero, zero_mul]
  · have h_inr : (![Sum.inr a, Sum.inr b] : Fin 2 → Fin 2 ⊕ Fin 2) =
        Sum.inr ∘ (![a, b] : Fin 2 → Fin 2) := by
      ext i
      fin_cases i <;> rfl
    rw [h_inr]
    have h_sum := sum_directSumRep_inr_two leftWeylRep rightWeylRep p.1 p.2
      diracEpsilon ![a, b]
    change (∑ β : Fin 2 → Fin 2 ⊕ Fin 2,
      (∏ i : Fin 2, (directSumRep leftWeylRep rightWeylRep).σ (p.1, p.2)
        (Sum.inr (![a, b] i)) (β i)) * diracEpsilon β) = _
    rw [h_sum]
    simp_rw [diracEpsilon_comp_inr, ← mul_assoc, mul_comm _ Complex.I, mul_assoc]
    rw [← Finset.mul_sum, sum_rightWeylRep_mul_weylEpsilon p ![a, b] ]

noncomputable def diracFermionConst : ∀ n : ℕ, (Fin n → Fin 2 ⊕ Fin 2) → ℂ
  | 0, _ => 1
  | 2, α => diracEpsilon α
  | _, _ => 0

@[simp]
lemma diracFermionConst_zero (α : Fin 0 → Fin 2 ⊕ Fin 2) : diracFermionConst 0 α = 1 := rfl

@[simp]
lemma diracFermionConst_one (α : Fin 1 → Fin 2 ⊕ Fin 2) : diracFermionConst 1 α = 0 := rfl

@[simp]
lemma diracFermionConst_two (α : Fin 2 → Fin 2 ⊕ Fin 2) :
    diracFermionConst 2 α = diracEpsilon α := rfl

@[simp]
lemma diracFermionConst_add_three (m : ℕ) (α : Fin (m + 3) → Fin 2 ⊕ Fin 2) :
    diracFermionConst (m + 3) α = 0 := rfl

theorem sum_diracRep_mul_diracFermionConst
    (n : ℕ) (p : SL2C × SL2C) (α : Fin n → Fin 2 ⊕ Fin 2) :
    (∑ β : Fin n → Fin 2 ⊕ Fin 2,
      (∏ i : Fin n, diracRep.σ p (α i) (β i)) * diracFermionConst n β) =
      diracFermionConst n α := by
  match n with
  | 0 =>
    have hα : α = Fin.elim0 := Subsingleton.elim _ _
    subst hα
    simp [diracFermionConst]
  | 1 =>
    simp [diracFermionConst]
  | 2 =>
    exact sum_diracRep_mul_diracEpsilon p α
  | m + 3 =>
    simp [diracFermionConst]

theorem diracFermionConst_eq_neg_one_pow_mul_rev
    (n : ℕ) (α : Fin n → Fin 2 ⊕ Fin 2) :
    diracFermionConst n α =
      ((-1 : ℂ) ^ (n * (n - 1) / 2)) * diracFermionConst n (α ∘ Fin.rev) := by
  match n with
  | 0 =>
    simp [diracFermionConst]
  | 1 =>
    simp [diracFermionConst]
  | 2 =>
    rw [two_mul_two_sub_one_div_two, pow_one]
    change diracEpsilon α = (-1 : ℂ) * diracEpsilon (α ∘ Fin.rev)
    rw [diracEpsilon_comp_rev]
    ring
  | m + 3 =>
    simp [diracFermionConst]

lemma chiralDoubleStarStructure_C_apply (R : HolomorphicLorentzRep ι) (hR : R.HasRealConj)
    (x y : ι ⊕ ι) :
    (chiralDoubleStarStructure R hR).C x y = if y = x.swap then 1 else 0 := by
  rcases x with i₁ | i₂ <;> rcases y with j₁ | j₂
  · simp [chiralDoubleStarStructure]
  · change (1 : Matrix ι ι ℂ) i₁ j₂ = if Sum.inr j₂ = Sum.inr i₁ then 1 else 0
    by_cases hij : i₁ = j₂
    · subst hij; simp
    · have hne : j₂ ≠ i₁ := Ne.symm hij
      simp [hij, hne]
  · change (1 : Matrix ι ι ℂ) i₂ j₁ = if Sum.inl j₁ = Sum.inl i₂ then 1 else 0
    by_cases hij : i₂ = j₁
    · subst hij; simp
    · have hne : j₁ ≠ i₂ := Ne.symm hij
      simp [hij, hne]
  · simp [chiralDoubleStarStructure]

lemma prod_chiralDoubleStarStructure_C (R : HolomorphicLorentzRep ι) (hR : R.HasRealConj)
    (n : ℕ) (α β : Fin n → ι ⊕ ι) :
    (∏ i : Fin n, (chiralDoubleStarStructure R hR).C (α i) (β i)) =
      if β = Sum.swap ∘ α then 1 else 0 := by
  simp_rw [chiralDoubleStarStructure_C_apply]
  by_cases hβ : β = Sum.swap ∘ α
  · subst hβ
    rw [if_pos rfl]
    exact Finset.prod_eq_one (fun i _ => if_pos rfl)
  · rw [if_neg hβ]
    have h_ex : ∃ i : Fin n, β i ≠ (α i).swap := by
      by_contra h_all
      exact hβ (funext fun i => Classical.not_not.mp fun hni => h_all ⟨i, hni⟩)
    rcases h_ex with ⟨i₀, hi₀⟩
    exact Finset.prod_eq_zero (Finset.mem_univ i₀) (if_neg hi₀)

@[simp]
lemma sum_prod_chiralDoubleStarStructure_C_mul (R : HolomorphicLorentzRep ι) (hR : R.HasRealConj)
    (n : ℕ) (α : Fin n → ι ⊕ ι) (G : (Fin n → ι ⊕ ι) → ℂ) :
    (∑ β : Fin n → ι ⊕ ι,
      (∏ i : Fin n, (chiralDoubleStarStructure R hR).C (α i) (β i)) * G β) =
      G (Sum.swap ∘ α) := by
  simp_rw [prod_chiralDoubleStarStructure_C, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]

theorem star_diracFermionConst (n : ℕ) (α : Fin n → Fin 2 ⊕ Fin 2) :
    star (diracFermionConst n α) =
      diracFermionConst n ((Sum.swap ∘ α) ∘ Fin.rev) := by
  match n with
  | 0 =>
    simp [diracFermionConst]
  | 1 =>
    simp [diracFermionConst]
  | 2 =>
    exact star_diracEpsilon α
  | m + 3 =>
    simp [diracFermionConst]

noncomputable def diracFermionS : SchwingerFamily (Fin 2 ⊕ Fin 2) :=
  fun n α _ => diracFermionConst n α

noncomputable def diracFermionH :
    ∀ n : ℕ, (Fin n → Fin 2 ⊕ Fin 2) → (Fin n → Fin 4 → ℂ) → ℂ :=
  fun n α _ => diracFermionConst n α

noncomputable def diracFermionW : WightmanFamily (Fin 2 ⊕ Fin 2) :=
  fun n α => diracFermionConst n α • schwartzIntegralCLM n

@[simp]
lemma diracFermionW_apply (n : ℕ) (α : Fin n → Fin 2 ⊕ Fin 2)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    diracFermionW n α f = diracFermionConst n α * ∫ x : Fin n → Fin 4 → ℝ, f x := rfl

@[simp]
theorem diracFermionW_unitIntegralSchwartz (n : ℕ) (α : Fin n → Fin 2 ⊕ Fin 2) :
    diracFermionW n α (unitIntegralSchwartz n) = diracFermionConst n α := by
  rw [diracFermionW_apply, integral_unitIntegralSchwartz, mul_one]

@[simp]
theorem diracFermionW_two_inl_zero_one :
    diracFermionW 2 ![Sum.inl 0, Sum.inl 1] (unitIntegralSchwartz 2) = Complex.I := by
  rw [diracFermionW_unitIntegralSchwartz, diracFermionConst_two,
      diracEpsilon_inl_inl, weylEpsilon_zero_one, mul_one]

theorem diracFermionW_twoPoint_nondegenerate :
    ∃ (α : Fin 2 → Fin 2 ⊕ Fin 2) (f : SchwartzMap (Fin 2 → Fin 4 → ℝ) ℂ),
      diracFermionW 2 α f ≠ 0 :=
  ⟨![Sum.inl 0, Sum.inl 1], unitIntegralSchwartz 2, by
    rw [diracFermionW_two_inl_zero_one]
    exact Complex.I_ne_zero⟩

noncomputable def diracFermionTubeExtension : TubeExtension diracFermionW where
  H := diracFermionH
  analytic _ _ := analyticOn_const
  boundary n α f v _hv := by
    have h_eq : (fun t : ℝ => ∫ x : Fin n → Fin 4 → ℝ,
        diracFermionH n α
          (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ)) * f x) =
        fun _ => diracFermionConst n α * ∫ x : Fin n → Fin 4 → ℝ, f x := by
      ext t
      dsimp [diracFermionH]
      exact integral_const_mul (diracFermionConst n α) f
    rw [h_eq, diracFermionW_apply]
    exact tendsto_const_nhds

@[simp]
lemma diracFermionTubeExtension_H : diracFermionTubeExtension.H = diracFermionH := rfl

@[simp]
theorem schwingerFromTube_diracFermionTubeExtension :
    schwingerFromTube diracFermionTubeExtension = diracFermionS := rfl

theorem diracFermionTubeBoundaryInjective :
    TubeBoundaryInjective diracFermionTubeExtension := by
  intro n α hW _z _hz
  have h_unit := hW (unitIntegralSchwartz n)
  rwa [diracFermionW_unitIntegralSchwartz] at h_unit

theorem diracFermionTubeTranslationInvariant :
    TubeTranslationInvariant diracFermionTubeExtension :=
  fun _ _ _ _ _ => rfl

theorem diracFermionTubeCovariant :
    TubeCovariant diracRep diracFermionTubeExtension := by
  intro n A z _hz _hAz α
  dsimp [diracFermionTubeExtension_H, diracFermionH, HolomorphicLorentzRep.rep_apply]
  exact (sum_diracRep_mul_diracFermionConst n (A, sl2c_conj A) α).symm

theorem diracFermionTubeWickHermiticity :
    TubeWickHermiticity diracStarStructure diracFermionTubeExtension := by
  intro n α z _hz _hz_rev
  dsimp [diracFermionTubeExtension_H, diracFermionH, diracStarStructure]
  rw [sum_prod_chiralDoubleStarStructure_C_mul leftWeylRep leftWeylRep_hasRealConj
      n α (fun β => diracFermionConst n (β ∘ Fin.rev))]
  exact star_diracFermionConst n α

theorem diracFermionOSHermiticity :
    OSHermiticity diracStarStructure diracFermionS :=
  schwingerFromTube_os_hermiticity diracStarStructure diracFermionTubeExtension
    diracFermionTubeWickHermiticity

theorem diracFermionTubeWeakLocality :
    TubeWeakLocality (-1) diracFermionTubeExtension := by
  intro n α z _hz
  dsimp [diracFermionTubeExtension_H, diracFermionH]
  exact diracFermionConst_eq_neg_one_pow_mul_rev n α

theorem diracFermionSpectrumCondition :
    SpectrumCondition diracFermionW := by
  intro n α f hf
  have h0 : minkowskiFourier f 0 = 0 := by
    rcases hf with ⟨U, _hU_open, hU_sub, hU_zero⟩ | h0
    · exact hU_zero 0 (hU_sub (zero_mem_spectralRegion n))
    · exact h0
  rw [minkowskiFourier_eval_zero_n] at h0
  rw [diracFermionW_apply, h0, mul_zero]

theorem diracFermionPoincareCovariant :
    PoincareCovariant diracRep diracFermionW := by
  intro n a A f f' hf' α
  have h_int : (∫ x : Fin n → Fin 4 → ℝ, f x) = ∫ x : Fin n → Fin 4 → ℝ, f' x := by
    have h_f : (fun x : Fin n → Fin 4 → ℝ => f x) =
        fun x => f' (fun i => poincareAct a A (x i)) := by
      ext x
      exact (hf' x).symm
    rw [h_f, integral_poincareAct_eq]
  have h_sum : ∀ β : Fin n → Fin 2 ⊕ Fin 2,
      (∏ i : Fin n, diracRep.rep A (α i) (β i)) * diracFermionW n β f =
        ((∏ i : Fin n, diracRep.σ (A, sl2c_conj A) (α i) (β i)) *
          diracFermionConst n β) * ∫ x : Fin n → Fin 4 → ℝ, f' x := by
    intro β
    rw [diracFermionW_apply, h_int, HolomorphicLorentzRep.rep_apply, mul_assoc]
  simp_rw [h_sum, ← Finset.sum_mul]
  rw [diracFermionW_apply, sum_diracRep_mul_diracFermionConst n (A, sl2c_conj A) α]

theorem diracFermionWeakLocality :
    WeakLocality (-1) diracFermionW := by
  intro n α f f' _hf_jost hf'
  rw [diracFermionW_apply, diracFermionW_apply]
  have h_f : (fun x : Fin n → Fin 4 → ℝ => f x) =
      fun x => f' (fun i => x (Fin.rev i)) := by
    ext x
    exact (hf' x).symm
  rw [h_f, integral_comp_rev, ← mul_assoc]
  congr 1
  exact diracFermionConst_eq_neg_one_pow_mul_rev n α

theorem diracFermionPCT :
    WightmanPCT (-1) diracRep diracFermionW :=
  wightman_pct_theorem diracRep diracFermionW
    diracFermionSpectrumCondition diracFermionPoincareCovariant diracFermionWeakLocality

theorem diracFermion_spin_statistics_unconditional
    {η : ℂ} (hloc : WeakLocality η diracFermionW) :
    η = -1 :=
  dirac_wightman_spin_statistics_unconditional diracFermionW
    diracFermionSpectrumCondition diracFermionPoincareCovariant hloc
    diracFermionW_twoPoint_nondegenerate

theorem not_diracFermion_bosonic_weakLocality :
    ¬ WeakLocality 1 diracFermionW := by
  intro hbos
  have h := diracFermion_spin_statistics_unconditional hbos
  norm_num at h

@[simp]
theorem tubeWickTimeDiff_two_neg_comp_rev (z : Fin 2 → Fin 4 → ℂ) :
    tubeWickTimeDiff 2 (-(z ∘ Fin.rev)) 0 (by decide) =
      tubeWickTimeDiff 2 z 0 (by decide) := by
  unfold tubeWickTimeDiff
  have h0 : Fin.rev (0 : Fin 2) = 1 := rfl
  have h1 : Fin.rev (1 : Fin 2) = 0 := rfl
  change -Complex.I * (-z (Fin.rev 1) 0 - -z (Fin.rev 0) 0) =
    -Complex.I * (z 1 0 - z 0 0)
  rw [h0, h1]
  ring

@[simp]
theorem spectralTwoPointTube_neg_comp_rev (E : ℝ) (z : Fin 2 → Fin 4 → ℂ) :
    spectralTwoPointTube E (-(z ∘ Fin.rev)) = spectralTwoPointTube E z := by
  unfold spectralTwoPointTube
  rw [tubeWickTimeDiff_two_neg_comp_rev]

@[simp]
theorem discreteKallenLehmannTube_neg_comp_rev
    (N : ℕ) (w E : Fin N → ℝ) (z : Fin 2 → Fin 4 → ℂ) :
    discreteKallenLehmannTube N w E (-(z ∘ Fin.rev)) =
      discreteKallenLehmannTube N w E z := by
  unfold discreteKallenLehmannTube
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [spectralTwoPointTube_neg_comp_rev]

@[simp]
theorem euclidSpectralTwoPoint_neg_comp_rev (E : ℝ) (x : Fin 2 → Fin 4 → ℝ) :
    euclidSpectralTwoPoint E (-(x ∘ Fin.rev)) = euclidSpectralTwoPoint E x := by
  unfold euclidSpectralTwoPoint
  have h0 : Fin.rev (0 : Fin 2) = 1 := rfl
  have h1 : Fin.rev (1 : Fin 2) = 0 := rfl
  change laplaceExp E (((-x (Fin.rev 1) 0 - -x (Fin.rev 0) 0 : ℝ) : ℂ)) =
    laplaceExp E ((x 1 0 - x 0 0 : ℝ) : ℂ)
  rw [h0, h1]
  congr 2
  ring

@[simp]
theorem discreteKallenLehmannEuclid_neg_comp_rev
    (N : ℕ) (w E : Fin N → ℝ) (x : Fin 2 → Fin 4 → ℝ) :
    discreteKallenLehmannEuclid N w E (-(x ∘ Fin.rev)) =
      discreteKallenLehmannEuclid N w E x := by
  unfold discreteKallenLehmannEuclid
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [euclidSpectralTwoPoint_neg_comp_rev]

@[simp]
theorem tubeWickTimeDiff_two_star_rev (z : Fin 2 → Fin 4 → ℂ) :
    tubeWickTimeDiff 2 (fun i μ => star (z (Fin.rev i) μ)) 0 (by decide) =
      star (tubeWickTimeDiff 2 z 0 (by decide)) := by
  unfold tubeWickTimeDiff
  have h0 : Fin.rev (0 : Fin 2) = 1 := rfl
  have h1 : Fin.rev (1 : Fin 2) = 0 := rfl
  change -Complex.I * (star (z (Fin.rev 1) 0) - star (z (Fin.rev 0) 0)) =
    star (-Complex.I * (z 1 0 - z 0 0))
  rw [h0, h1, star_mul', star_sub, Complex.star_def, map_neg, Complex.conj_I, ← Complex.star_def]
  ring

theorem star_spectralTwoPointTube (E : ℝ) (z : Fin 2 → Fin 4 → ℂ) :
    star (spectralTwoPointTube E z) =
      spectralTwoPointTube E (fun i μ => star (z (Fin.rev i) μ)) := by
  unfold spectralTwoPointTube
  rw [tubeWickTimeDiff_two_star_rev, laplaceExp_star]

theorem star_discreteKallenLehmannTube
    (N : ℕ) (w E : Fin N → ℝ) (z : Fin 2 → Fin 4 → ℂ) :
    star (discreteKallenLehmannTube N w E z) =
      discreteKallenLehmannTube N w E (fun i μ => star (z (Fin.rev i) μ)) := by
  unfold discreteKallenLehmannTube
  rw [star_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [star_mul', Complex.star_def, Complex.conj_ofReal, ← Complex.star_def,
      star_spectralTwoPointTube]

theorem norm_discreteKallenLehmannTube_le
    {N : ℕ} {w : Fin N → ℝ} (hw : ∀ a : Fin N, 0 ≤ w a)
    {E : Fin N → ℝ} (hE : ∀ a : Fin N, 0 ≤ E a)
    {z : Fin 2 → Fin 4 → ℂ} (hz : z ∈ forward_tube_n 2) :
    ‖discreteKallenLehmannTube N w E z‖ ≤ ∑ a : Fin N, w a := by
  unfold discreteKallenLehmannTube
  refine (norm_sum_le Finset.univ _).trans (Finset.sum_le_sum (fun a _ => ?_))
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hw a)]
  have h_le := norm_spectralTwoPointTube_le_one (hE a) hz
  nlinarith [hw a]

theorem norm_multiPointKallenLehmannTube_le
    {n N : ℕ} {w : Fin N → ℝ} (hw : ∀ a : Fin N, 0 ≤ w a)
    {E : Fin N → Fin (n - 1) → ℝ} (hE : ∀ (a : Fin N) (i : Fin (n - 1)), 0 ≤ E a i)
    {z : Fin n → Fin 4 → ℂ} (hz : z ∈ forward_tube_n n) :
    ‖multiPointKallenLehmannTube n N w E z‖ ≤ ∑ a : Fin N, w a := by
  unfold multiPointKallenLehmannTube
  refine (norm_sum_le Finset.univ _).trans (Finset.sum_le_sum (fun a _ => ?_))
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hw a)]
  have h_le := norm_spectralMultiPointTube_le_one (hE a) hz
  nlinarith [hw a]

theorem vladimirovKernel_diracRep_one_self_eq_zero
    (W : WightmanFamily (Fin 2 ⊕ Fin 2))
    (hspec : SpectrumCondition W) (hP : PoincareCovariant diracRep W)
    (c : Fin 2 ⊕ Fin 2) :
    vladimirovKernel diracStarStructure W 1 1 (fun _ => c) (fun _ => c) = 0 := by
  unfold vladimirovKernel
  change (∑ β : Fin 1 → Fin 2 ⊕ Fin 2,
    (∏ i : Fin 1, (chiralDoubleStarStructure leftWeylRep leftWeylRep_hasRealConj).C
      c (β i)) *
      vladimirov_H W (1 + 1) (Fin.append (β ∘ Fin.rev) (fun _ => c)) 0) = 0
  rw [sum_prod_chiralDoubleStarStructure_C_mul leftWeylRep leftWeylRep_hasRealConj
      1 (fun _ => c) (fun β => vladimirov_H W (1 + 1) (Fin.append (β ∘ Fin.rev) (fun _ => c)) 0)]
  have h_idx : Fin.append ((Sum.swap ∘ fun _ : Fin 1 => c) ∘ Fin.rev) (fun _ : Fin 1 => c) =
      ![c.swap, c] := by
    ext i
    fin_cases i <;> rfl
  rw [h_idx]
  rcases c with a | a
  · exact vladimirov_H_zero_diracRep_inr_inl_eq_zero W hspec hP a a
  · exact vladimirov_H_zero_diracRep_inl_inr_eq_zero W hspec hP a a

theorem vacPositivity_of_osData (R : HolomorphicLorentzRep ι) (S : StarStructure R) :
    Positivity S (vacW (ι := ι)) :=
  positivity_of_osReflectionPositiveData (vacOSData R S)
    vacSpectrumCondition vladimirovSchwinger_vacW.symm

theorem z2FreePositivity_of_osData :
    Positivity trivialStarStructure z2FreeW :=
  positivity_of_osReflectionPositiveData z2FreeOSData
    (momentSpectrumCondition z2FreeCoeff)
    (vladimirovSchwinger_momentW z2FreeCoeff).symm

noncomputable def vacEuclideanTubeBridgeOfOSData
    (R : HolomorphicLorentzRep ι) (S : StarStructure R) (η : ℂ) :
    OSEuclideanTubeBridge R S η vacS :=
  vladimirovEuclideanTubeBridgeOfOSData R S (vacOSData R S) vacW
    vacSpectrumCondition (vacPoincareCovariant R) (vacWeakLocality η)
    (fun n α x _ => by rw [vladimirovSchwinger_vacW]; rfl)

noncomputable def z2FreeEuclideanTubeBridgeOfOSData :
    OSEuclideanTubeBridge trivialRep trivialStarStructure 1 z2FreeS :=
  vladimirovEuclideanTubeBridgeOfOSData trivialRep trivialStarStructure
    z2FreeOSData z2FreeW
    (momentSpectrumCondition z2FreeCoeff)
    (momentPoincareCovariant z2FreeCoeff)
    (momentWeakLocality z2FreeCoeff)
    (fun n α x _ => by
      change z2FreeS n α x = vladimirovSchwinger (momentW z2FreeCoeff) n α x
      rw [vladimirovSchwinger_momentW]
      rfl)

theorem wightman_diracRep_eq_zero_of_positivity
    (W : WightmanFamily (Fin 2 ⊕ Fin 2))
    (hspec : SpectrumCondition W) (hP : PoincareCovariant diracRep W)
    (hpos : Positivity diracStarStructure W)
    (n : ℕ) (hn : 1 ≤ n) (α : Fin n → Fin 2 ⊕ Fin 2)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    W n α f = 0 :=
  wightman_eq_zero_of_onePoint_vladimirovKernel_eq_zero diracStarStructure W hspec hpos
    (vladimirovKernel_diracRep_one_self_eq_zero W hspec hP) n hn α f

theorem not_diracFermionW_positivity :
    ¬ Positivity diracStarStructure diracFermionW := by
  intro hpos
  rcases diracFermionW_twoPoint_nondegenerate with ⟨α, f, hne⟩
  exact hne (wightman_diracRep_eq_zero_of_positivity diracFermionW
    diracFermionSpectrumCondition diracFermionPoincareCovariant hpos 2 (by omega) α f)

@[simp]
theorem vladimirov_H_zero_weylFermionW (n : ℕ) (α : Fin n → Fin 2) :
    vladimirov_H weylFermionW n α 0 = weylFermionConst n α := by
  have h := W_n_eq_vladimirov_H_zero_mul_integral
    weylFermionSpectrumCondition n α (unitIntegralSchwartz n)
  rw [weylFermionW_unitIntegralSchwartz, integral_unitIntegralSchwartz, mul_one] at h
  exact h.symm

@[simp]
theorem vladimirovSchwinger_weylFermionW :
    vladimirovSchwinger weylFermionW = weylFermionS := by
  ext n α x
  rw [vladimirovSchwinger_eq_zero_eval weylFermionSpectrumCondition,
      vladimirov_H_zero_weylFermionW]
  rfl

@[simp]
theorem vladimirov_H_zero_diracFermionW (n : ℕ) (α : Fin n → Fin 2 ⊕ Fin 2) :
    vladimirov_H diracFermionW n α 0 = diracFermionConst n α := by
  have h := W_n_eq_vladimirov_H_zero_mul_integral
    diracFermionSpectrumCondition n α (unitIntegralSchwartz n)
  rw [diracFermionW_unitIntegralSchwartz, integral_unitIntegralSchwartz, mul_one] at h
  exact h.symm

@[simp]
theorem vladimirovSchwinger_diracFermionW :
    vladimirovSchwinger diracFermionW = diracFermionS := by
  ext n α x
  rw [vladimirovSchwinger_eq_zero_eval diracFermionSpectrumCondition,
      vladimirov_H_zero_diracFermionW]
  rfl

theorem not_diracFermionS_osReflectionPositive :
    ¬ OSReflectionPositive diracStarStructure diracFermionS := by
  intro hrp
  apply not_diracFermionW_positivity
  exact positivity_of_osReflectionPositiveData
    { 𝒮 := diracFermionS
      hermiticity := diracFermionOSHermiticity
      positivity := hrp }
    diracFermionSpectrumCondition vladimirovSchwinger_diracFermionW.symm

theorem weylFermion_os0_smooth (n : ℕ) (α : Fin n → Fin 2) :
    ContDiffOn ℝ (⊤ : ℕ∞) (weylFermionS n α) (orderedEuclidN n) :=
  schwingerFromTube_contDiffOn weylFermionTubeExtension n α

theorem weylFermion_os1_translation :
    OSTranslationInvariant weylFermionS :=
  schwingerFromTube_translation_invariant weylFermionTubeExtension
    weylFermionTubeTranslationInvariant

theorem weylFermion_os1_rotation
    (n : ℕ) (U V : SU2) (x : Fin n → Fin 4 → ℝ)
    (hx : x ∈ orderedEuclidN n) (hRx : euclidRotN n U V x ∈ orderedEuclidN n)
    (α : Fin n → Fin 2) :
    weylFermionS n α (euclidRotN n U V x) =
      ∑ β : Fin n → Fin 2,
        (∏ i : Fin n, leftWeylRep.σ (su2ToSL2C U, su2ToSL2C V) (α i) (β i)) *
          weylFermionS n β x :=
  schwingerFromTube_euclidCovariant leftWeylRep weylFermionW
    weylFermionTubeExtension weylFermionTubeCovariant n U V x hx hRx α

theorem weylFermion_os3_symmetry
    (n : ℕ) (α : Fin n → Fin 2) (x : Fin n → Fin 4 → ℝ) (hx : x ∈ orderedEuclidN n) :
    weylFermionS n α (-(x ∘ Fin.rev)) =
      (-1 : ℂ) ^ (n * (n - 1) / 2) * weylFermionS n (α ∘ Fin.rev) x :=
  schwingerFromTube_weakLocality weylFermionTubeExtension
    weylFermionTubeWeakLocality n α x hx

theorem weylFermion_euclid_spin_statistics {η : ℂ}
    (hsym : ∀ (n : ℕ) (α : Fin n → Fin 2) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n →
      weylFermionS n α (-(x ∘ Fin.rev)) =
        η ^ (n * (n - 1) / 2) * weylFermionS n (α ∘ Fin.rev) x) :
    η = -1 := by
  have hloc : WeakLocality η weylFermionW := by
    rw [vladimirovSchwinger_weakLocality_iff leftWeylRep weylFermionW
        weylFermionSpectrumCondition weylFermionPoincareCovariant,
        vladimirovSchwinger_weylFermionW]
    exact hsym
  exact weylFermion_spin_statistics_unconditional hloc

theorem diracFermion_os0_smooth (n : ℕ) (α : Fin n → Fin 2 ⊕ Fin 2) :
    ContDiffOn ℝ (⊤ : ℕ∞) (diracFermionS n α) (orderedEuclidN n) :=
  schwingerFromTube_contDiffOn diracFermionTubeExtension n α

theorem diracFermion_os1_translation :
    OSTranslationInvariant diracFermionS :=
  schwingerFromTube_translation_invariant diracFermionTubeExtension
    diracFermionTubeTranslationInvariant

theorem diracFermion_os1_rotation
    (n : ℕ) (U V : SU2) (x : Fin n → Fin 4 → ℝ)
    (hx : x ∈ orderedEuclidN n) (hRx : euclidRotN n U V x ∈ orderedEuclidN n)
    (α : Fin n → Fin 2 ⊕ Fin 2) :
    diracFermionS n α (euclidRotN n U V x) =
      ∑ β : Fin n → Fin 2 ⊕ Fin 2,
        (∏ i : Fin n, diracRep.σ (su2ToSL2C U, su2ToSL2C V) (α i) (β i)) *
          diracFermionS n β x :=
  schwingerFromTube_euclidCovariant diracRep diracFermionW
    diracFermionTubeExtension diracFermionTubeCovariant n U V x hx hRx α

theorem diracFermion_os3_symmetry
    (n : ℕ) (α : Fin n → Fin 2 ⊕ Fin 2) (x : Fin n → Fin 4 → ℝ)
    (hx : x ∈ orderedEuclidN n) :
    diracFermionS n α (-(x ∘ Fin.rev)) =
      (-1 : ℂ) ^ (n * (n - 1) / 2) * diracFermionS n (α ∘ Fin.rev) x :=
  schwingerFromTube_weakLocality diracFermionTubeExtension
    diracFermionTubeWeakLocality n α x hx

theorem diracFermion_euclid_spin_statistics {η : ℂ}
    (hsym : ∀ (n : ℕ) (α : Fin n → Fin 2 ⊕ Fin 2) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n →
      diracFermionS n α (-(x ∘ Fin.rev)) =
        η ^ (n * (n - 1) / 2) * diracFermionS n (α ∘ Fin.rev) x) :
    η = -1 := by
  have hloc : WeakLocality η diracFermionW := by
    rw [vladimirovSchwinger_weakLocality_iff diracRep diracFermionW
        diracFermionSpectrumCondition diracFermionPoincareCovariant,
        vladimirovSchwinger_diracFermionW]
    exact hsym
  exact diracFermion_spin_statistics_unconditional hloc

theorem diracOSReconstructedWightman_wightman_eq_zero
    {η : ℂ} {𝒮 : SchwingerFamily (Fin 2 ⊕ Fin 2)}
    (P : DiracOSReconstructedWightman η 𝒮)
    (n : ℕ) (hn : 1 ≤ n) (α : Fin n → Fin 2 ⊕ Fin 2)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    P.W n α f = 0 :=
  wightman_diracRep_eq_zero_of_positivity P.W P.spectrum P.poincare P.positivity n hn α f

theorem diracOSReconstructedWightman_eq_vacW
    {η : ℂ} {𝒮 : SchwingerFamily (Fin 2 ⊕ Fin 2)}
    (P : DiracOSReconstructedWightman η 𝒮) (hnorm : OSVacuumNormalized 𝒮)
    (hinj : TubeBoundaryInjective P.E) :
    P.W = vacW :=
  (P.wightman_eq_vacW_iff_twoPoint_wightman_eq_zero hnorm hinj).mpr
    (fun β f => diracOSReconstructedWightman_wightman_eq_zero P 2 (by omega) β f)

@[simp]
theorem measureKallenLehmannTube_neg_comp_rev
    {A : Type*} [MeasurableSpace A] (μ : Measure A) (w E : A → ℝ)
    (z : Fin 2 → Fin 4 → ℂ) :
    measureKallenLehmannTube μ w E (-(z ∘ Fin.rev)) =
      measureKallenLehmannTube μ w E z := by
  unfold measureKallenLehmannTube
  simp_rw [spectralTwoPointTube_neg_comp_rev]

@[simp]
theorem measureKallenLehmannEuclid_neg_comp_rev
    {A : Type*} [MeasurableSpace A] (μ : Measure A) (w E : A → ℝ)
    (x : Fin 2 → Fin 4 → ℝ) :
    measureKallenLehmannEuclid μ w E (-(x ∘ Fin.rev)) =
      measureKallenLehmannEuclid μ w E x := by
  unfold measureKallenLehmannEuclid
  simp_rw [euclidSpectralTwoPoint_neg_comp_rev]

theorem star_measureKallenLehmannTube
    {A : Type*} [MeasurableSpace A] (μ : Measure A) (w E : A → ℝ)
    (z : Fin 2 → Fin 4 → ℂ) :
    star (measureKallenLehmannTube μ w E z) =
      measureKallenLehmannTube μ w E (fun i μ => star (z (Fin.rev i) μ)) := by
  unfold measureKallenLehmannTube
  rw [Complex.star_def, ← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall (fun a => ?_))
  dsimp
  rw [← Complex.star_def, star_mul', Complex.star_def, Complex.conj_ofReal,
      ← Complex.star_def, star_spectralTwoPointTube]

@[simp]
theorem measureKallenLehmannTube_count_eq_discreteKallenLehmannTube
    (N : ℕ) (w E : Fin N → ℝ) (z : Fin 2 → Fin 4 → ℂ) :
    measureKallenLehmannTube Measure.count w E z =
      discreteKallenLehmannTube N w E z := by
  unfold measureKallenLehmannTube discreteKallenLehmannTube
  exact integral_fintype_count _

@[simp]
theorem measureKallenLehmannEuclid_count_eq_discreteKallenLehmannEuclid
    (N : ℕ) (w E : Fin N → ℝ) (x : Fin 2 → Fin 4 → ℝ) :
    measureKallenLehmannEuclid Measure.count w E x =
      discreteKallenLehmannEuclid N w E x := by
  unfold measureKallenLehmannEuclid discreteKallenLehmannEuclid
  exact integral_fintype_count _

noncomputable def vacSpectralMeasure
    (R : HolomorphicLorentzRep ι) (S : StarStructure R) :
    OSSpectralMeasure (vacOSData R S) (vacOSContraction R S) (Fin 1) :=
  (vacSpectralDecomposition R S).toOSSpectralMeasure

noncomputable def z2FreeSpectralMeasure :
    OSSpectralMeasure z2FreeOSData z2FreeOSContraction (Fin 2) :=
  z2FreeSpectralDecomposition.toOSSpectralMeasure

@[simp]
theorem vacSpectralMeasure_twoPointTubePropagator_eq
    (R : HolomorphicLorentzRep ι) (S : StarStructure R)
    (htrans : OSTranslationInvariant (vacOSData R S).𝒮)
    (Ψ Φ : OSHilbert (vacOSData R S))
    (b : Fin 3 → ℝ) (z : Fin 2 → Fin 4 → ℂ) :
    (vacSpectralMeasure R S).twoPointTubePropagator htrans Ψ Φ b z =
      (vacSpectralDecomposition R S).twoPointTubePropagator htrans Ψ Φ b z :=
  (vacSpectralDecomposition R S).toOSSpectralMeasure_twoPointTubePropagator htrans Ψ Φ b z

@[simp]
theorem z2FreeSpectralMeasure_twoPointTubePropagator_eq
    (htrans : OSTranslationInvariant z2FreeOSData.𝒮)
    (Ψ Φ : OSHilbert z2FreeOSData)
    (b : Fin 3 → ℝ) (z : Fin 2 → Fin 4 → ℂ) :
    z2FreeSpectralMeasure.twoPointTubePropagator htrans Ψ Φ b z =
      z2FreeSpectralDecomposition.twoPointTubePropagator htrans Ψ Φ b z :=
  z2FreeSpectralDecomposition.toOSSpectralMeasure_twoPointTubePropagator htrans Ψ Φ b z

theorem vacSpectralMeasure_diag_zero_eq_discreteKallenLehmannTube
    (R : HolomorphicLorentzRep ι) (S : StarStructure R)
    (htrans : OSTranslationInvariant (vacOSData R S).𝒮)
    (Ψ : OSHilbert (vacOSData R S)) (z : Fin 2 → Fin 4 → ℂ) :
    (vacSpectralMeasure R S).twoPointTubePropagator htrans Ψ Ψ 0 z =
      discreteKallenLehmannTube 1
        (fun a => ‖(vacSpectralMeasure R S).P a Ψ‖ ^ 2)
        (vacSpectralMeasure R S).E z := by
  rw [(vacSpectralMeasure R S).twoPointTubePropagator_diag_zero_eq_measureKallenLehmannTube]
  exact measureKallenLehmannTube_count_eq_discreteKallenLehmannTube 1 _ _ z

theorem z2FreeSpectralMeasure_diag_zero_eq_discreteKallenLehmannTube
    (htrans : OSTranslationInvariant z2FreeOSData.𝒮)
    (Ψ : OSHilbert z2FreeOSData) (z : Fin 2 → Fin 4 → ℂ) :
    z2FreeSpectralMeasure.twoPointTubePropagator htrans Ψ Ψ 0 z =
      discreteKallenLehmannTube 2
        (fun a => ‖z2FreeSpectralMeasure.P a Ψ‖ ^ 2)
        z2FreeSpectralMeasure.E z := by
  rw [z2FreeSpectralMeasure.twoPointTubePropagator_diag_zero_eq_measureKallenLehmannTube]
  exact measureKallenLehmannTube_count_eq_discreteKallenLehmannTube 2 _ _ z

end
end QFT
