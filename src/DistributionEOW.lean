import Mathlib.Analysis.Distribution.Distribution
import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Topology.Sets.Opens
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import SCVAnalysis
import Mathlib.Analysis.Complex.OperatorNorm

open Set TopologicalSpace ContinuousLinearMap QFT MeasureTheory Metric Complex Analysis
open scoped Distributions Manifold NNReal

namespace Distribution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
variable [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
variable (Ω : Opens E)

def VanishesOn (T : 𝓓'(Ω, F)) (U : Opens E) (_ : (U : Set E) ⊆ (Ω : Set E)) : Prop :=
  ∀ f : 𝓓(Ω, ℝ), tsupport (fun x => f x) ⊆ (U : Set E) → T f = 0

def support (T : 𝓓'(Ω, F)) : Set E :=
  (Ω : Set E) \ ⋃ (U : Opens E) (hU : (U : Set E) ⊆ (Ω : Set E))
    (_ : VanishesOn Ω T U hU), (U : Set E)

omit [FiniteDimensional ℝ E] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] in
lemma compl_support_eq (T : 𝓓'(Ω, F)) :
    (Ω : Set E) \ Distribution.support Ω T =
    ⋃ (U : Opens E) (hU : (U : Set E) ⊆ (Ω : Set E)) (_ : VanishesOn Ω T U hU), (U : Set E) := by
  rw [Distribution.support]
  have h_sub : (⋃ (U : Opens E) (hU : (U : Set E) ⊆ (Ω : Set E))
      (_ : VanishesOn Ω T U hU), (U : Set E)) ⊆ (Ω : Set E) := by
    intro x hx
    simp only [mem_iUnion] at hx
    rcases hx with ⟨U, hU, _, hxU⟩
    exact hU hxU
  exact sdiff_sdiff_cancel_left h_sub

omit [FiniteDimensional ℝ E] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] in
lemma isOpen_compl_support (T : 𝓓'(Ω, F)) : IsOpen ((Ω : Set E) \ Distribution.support Ω T) := by
  rw [compl_support_eq]
  apply isOpen_iUnion
  intro U
  apply isOpen_iUnion
  intro _
  apply isOpen_iUnion
  intro _
  exact U.isOpen

def HasCompactSupport (T : 𝓓'(Ω, F)) : Prop :=
  IsCompact (Distribution.support Ω T)

def VanishIndex (T : 𝓓'(Ω, F)) :=
  { U : Opens E // ∃ (hU : (U : Set E) ⊆ (Ω : Set E)), VanishesOn Ω T U hU }

def VanishCover (T : 𝓓'(Ω, F)) (i : VanishIndex Ω T) : Set E :=
  (i.1 : Set E)

omit [FiniteDimensional ℝ E] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] in
lemma isOpen_VanishCover (T : 𝓓'(Ω, F)) (i : VanishIndex Ω T) : IsOpen (VanishCover Ω T i) :=
  i.1.isOpen

omit [FiniteDimensional ℝ E] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] in
lemma iUnion_VanishCover_eq (T : 𝓓'(Ω, F)) :
    ⋃ i : VanishIndex Ω T, VanishCover Ω T i = (Ω : Set E) \ Distribution.support Ω T := by
  rw [compl_support_eq]
  ext x
  simp only [VanishCover, mem_iUnion]
  constructor
  · rintro ⟨⟨U, hU, hV⟩, hx⟩
    exact ⟨U, hU, hV, hx⟩
  · rintro ⟨U, hU, hV, hx⟩
    exact ⟨⟨U, hU, hV⟩, hx⟩

noncomputable def pouTestFunc (T : 𝓓'(Ω, F)) (f : 𝓓(Ω, ℝ))
    (p : SmoothPartitionOfUnity (VanishIndex Ω T) 𝓘(ℝ, E) E (tsupport (fun x => f x)))
    (i : VanishIndex Ω T) : 𝓓(Ω, ℝ) :=
  {
    toFun := fun x => p i x * f x
    contDiff' := ContDiff.mul (ContMDiff.contDiff (p i).contMDiff) f.contDiff'
    hasCompactSupport' := by
      apply HasCompactSupport.of_support_subset_isCompact f.hasCompactSupport'
      intro x hx
      simp only [Function.mem_support, ne_eq] at hx
      apply subset_closure
      simp only [Function.mem_support, ne_eq]
      intro h_f
      exact hx (by rw [show f x = 0 from h_f, mul_zero])
    tsupport_subset' := by
      calc
        tsupport (fun x => p i x * f x) ⊆ tsupport (fun x => f x) := by
          apply closure_mono
          intro x hx
          simp only [Function.mem_support, ne_eq] at hx
          simp only [Function.mem_support, ne_eq]
          intro h_f
          exact hx (by rw [show f x = 0 from h_f, mul_zero])
        _ ⊆ (Ω : Set E) := f.tsupport_subset'
  }

omit [FiniteDimensional ℝ E] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] in
lemma pouTestFunc_tsupport_subset (T : 𝓓'(Ω, F)) (f : 𝓓(Ω, ℝ))
    (p : SmoothPartitionOfUnity (VanishIndex Ω T) 𝓘(ℝ, E) E (tsupport (fun x => f x)))
    (hp_sub : p.IsSubordinate (VanishCover Ω T)) (i : VanishIndex Ω T) :
    tsupport (fun x => (pouTestFunc Ω T f p i) x) ⊆ VanishCover Ω T i := by
  calc
    tsupport (fun x => p i x * f x) ⊆ tsupport (p i) := by
      apply closure_mono
      intro x hx
      simp only [Function.mem_support, ne_eq] at hx
      simp only [Function.mem_support, ne_eq]
      intro h_p
      exact hx (by rw [show p i x = 0 from h_p, zero_mul])
    _ ⊆ VanishCover Ω T i := hp_sub i

omit [FiniteDimensional ℝ E] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] in
lemma pouTestFunc_eval_zero (T : 𝓓'(Ω, F)) (f : 𝓓(Ω, ℝ))
    (p : SmoothPartitionOfUnity (VanishIndex Ω T) 𝓘(ℝ, E) E (tsupport (fun x => f x)))
    (hp_sub : p.IsSubordinate (VanishCover Ω T)) (i : VanishIndex Ω T) :
    T (pouTestFunc Ω T f p i) = 0 := by
  have h_supp := pouTestFunc_tsupport_subset Ω T f p hp_sub i
  have h_ex := i.2
  rcases h_ex with ⟨hU, h_vanish⟩
  exact h_vanish (pouTestFunc Ω T f p i) h_supp

noncomputable def POUFinset (T : 𝓓'(Ω, F)) (f : 𝓓(Ω, ℝ))
    (p : SmoothPartitionOfUnity (VanishIndex Ω T) 𝓘(ℝ, E) E (tsupport (fun x => f x))) :
    Finset (VanishIndex Ω T) :=
  (p.locallyFinite.finite_nonempty_inter_compact f.hasCompactSupport').toFinset

omit [FiniteDimensional ℝ E] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] in
lemma pou_sum_eq (T : 𝓓'(Ω, F)) (f : 𝓓(Ω, ℝ))
    (p : SmoothPartitionOfUnity (VanishIndex Ω T) 𝓘(ℝ, E) E (tsupport (fun x => f x))) (x : E) :
    ∑ i ∈ POUFinset Ω T f p, p i x * f x = f x := by
  by_cases hf : f x = 0
  · rw [hf]
    simp only [mul_zero, Finset.sum_const_zero]
  · have hx_supp : x ∈ tsupport (fun x => f x) := subset_closure hf
    have h_sum1 := p.sum_eq_one hx_supp
    have h_finsum : ∑ᶠ i, p i x = ∑ i ∈ POUFinset Ω T f p, p i x := by
      apply finsum_eq_sum_of_support_subset
      intro i hi
      have h_nonempty : (Function.support (p i) ∩ tsupport (fun x => f x)).Nonempty :=
        ⟨x, ⟨hi, hx_supp⟩⟩
      have h_mem : i ∈ POUFinset Ω T f p := by
        simp only [POUFinset, Finite.mem_toFinset, mem_setOf_eq]
        exact h_nonempty
      exact h_mem
    rw [h_finsum] at h_sum1
    calc
      ∑ i ∈ POUFinset Ω T f p, p i x * f x = (∑ i ∈ POUFinset Ω T f p, p i x) * f x := by
        rw [Finset.sum_mul]
      _ = 1 * f x := by rw [h_sum1]
      _ = f x := by rw [one_mul]

omit [FiniteDimensional ℝ E] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] in
lemma pou_sum_eq_testFunc (T : 𝓓'(Ω, F)) (f : 𝓓(Ω, ℝ))
    (p : SmoothPartitionOfUnity (VanishIndex Ω T) 𝓘(ℝ, E) E (tsupport (fun x => f x))) :
    ∑ i ∈ POUFinset Ω T f p, pouTestFunc Ω T f p i = f := by
  ext x
  have h_sum : (∑ i ∈ POUFinset Ω T f p, pouTestFunc Ω T f p i) x =
      ∑ i ∈ POUFinset Ω T f p, (pouTestFunc Ω T f p i) x := by
    simp
  rw [h_sum]
  exact pou_sum_eq Ω T f p x

omit [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] in
lemma vanishing_on_disjoint_support (T : 𝓓'(Ω, F)) (f : 𝓓(Ω, ℝ))
    (h_disj : tsupport (fun x => f x) ⊆ (Ω : Set E) \ Distribution.support Ω T) : T f = 0 := by
  have h_K_closed : IsClosed (tsupport (fun x => f x)) := isClosed_closure
  have h_cov : tsupport (fun x => f x) ⊆ ⋃ i : VanishIndex Ω T, VanishCover Ω T i := by
    rw [iUnion_VanishCover_eq]
    exact h_disj
  rcases SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, E) h_K_closed
    (VanishCover Ω T) (isOpen_VanishCover Ω T) h_cov with ⟨p, hp_sub⟩
  have h_decomp := pou_sum_eq_testFunc Ω T f p
  rw [← h_decomp]
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro i _
  exact pouTestFunc_eval_zero Ω T f p hp_sub i

noncomputable def applySmoothFun (T : 𝓓'(Ω, F)) (_ : HasCompactSupport Ω T)
    (ψ : E → ℝ) (hψ : ContDiff ℝ (↑(⊤ : ℕ∞)) ψ)
    (V : Opens E) (_ : Distribution.support Ω T ⊆ (V : Set E))
    (χ : 𝓓(Ω, ℝ)) (_ : ∀ x ∈ (V : Set E), χ x = 1) : 𝓓(Ω, ℝ) :=
  {
    toFun := fun x => χ.toFun x * ψ x
    contDiff' := by
      exact ContDiff.mul χ.contDiff' hψ
    hasCompactSupport' := by
      apply HasCompactSupport.of_support_subset_isCompact χ.hasCompactSupport'
      intro x hx
      apply subset_closure
      intro h
      apply hx
      dsimp only
      have h_toFun : χ.toFun x = 0 := h
      rw [h_toFun, zero_mul]
    tsupport_subset' := by
      calc
        tsupport (fun x => χ.toFun x * ψ x) ⊆ tsupport χ := by
          apply closure_mono
          intro x hx h
          apply hx
          dsimp only
          have h_toFun : χ.toFun x = 0 := h
          rw [h_toFun, zero_mul]
        _ ⊆ Ω := χ.tsupport_subset'
  }

noncomputable def applySmooth (T : 𝓓'(Ω, F)) (hT : HasCompactSupport Ω T)
    (ψ : E → ℝ) (hψ : ContDiff ℝ (↑(⊤ : ℕ∞)) ψ)
    (V : Opens E) (hV : Distribution.support Ω T ⊆ (V : Set E))
    (χ : 𝓓(Ω, ℝ)) (hχ_one : ∀ x ∈ (V : Set E), χ x = 1) : F :=
  T (applySmoothFun Ω T hT ψ hψ V hV χ hχ_one)

omit [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] in
lemma applySmooth_indep (T : 𝓓'(Ω, F)) (hT : HasCompactSupport Ω T)
    (ψ : E → ℝ) (hψ : ContDiff ℝ (↑(⊤ : ℕ∞)) ψ)
    (V₁ V₂ : Opens E)
    (hV₁ : Distribution.support Ω T ⊆ (V₁ : Set E))
    (hV₂ : Distribution.support Ω T ⊆ (V₂ : Set E))
    (χ₁ χ₂ : 𝓓(Ω, ℝ))
    (hχ₁ : ∀ x ∈ (V₁ : Set E), χ₁ x = 1)
    (hχ₂ : ∀ x ∈ (V₂ : Set E), χ₂ x = 1) :
    applySmooth Ω T hT ψ hψ V₁ hV₁ χ₁ hχ₁ = applySmooth Ω T hT ψ hψ V₂ hV₂ χ₂ hχ₂ := by
  let F₁ := applySmoothFun Ω T hT ψ hψ V₁ hV₁ χ₁ hχ₁
  let F₂ := applySmoothFun Ω T hT ψ hψ V₂ hV₂ χ₂ hχ₂
  have h_eq : T F₁ - T F₂ = 0 := by
    rw [← map_sub T F₁ F₂]
    apply vanishing_on_disjoint_support
    let S := {x : E | χ₁.toFun x * ψ x - χ₂.toFun x * ψ x ≠ 0}
    have hS : S ⊆ (V₁ : Set E)ᶜ ∪ (V₂ : Set E)ᶜ := by
      intro x hx
      have hx_prop : χ₁.toFun x * ψ x - χ₂.toFun x * ψ x ≠ 0 := hx
      by_contra h
      simp only [mem_union, mem_compl_iff] at h
      push Not at h
      have h1 := hχ₁ x h.1
      have h2 := hχ₂ x h.2
      have h_eval : χ₁.toFun x * ψ x - χ₂.toFun x * ψ x = 1 * ψ x - 1 * ψ x := by
        rw [show χ₁.toFun x = 1 from h1, show χ₂.toFun x = 1 from h2]
      rw [h_eval, sub_self] at hx_prop
      exact hx_prop rfl
    have h_closed : IsClosed ((V₁ : Set E)ᶜ ∪ (V₂ : Set E)ᶜ) := by
      apply IsClosed.union
      · exact V₁.isOpen.isClosed_compl
      · exact V₂.isOpen.isClosed_compl
    have h_closure : closure S ⊆ (V₁ : Set E)ᶜ ∪ (V₂ : Set E)ᶜ := closure_minimal hS h_closed
    have h_subset_Ω : closure S ⊆ (Ω : Set E) := by
      calc
        closure S ⊆ closure (Function.support (fun x => χ₁.toFun x) ∪
          Function.support (fun x => χ₂.toFun x)) := by
          apply closure_mono
          intro x hx
          have hx_prop : χ₁.toFun x * ψ x - χ₂.toFun x * ψ x ≠ 0 := hx
          have h_not_zero : χ₁.toFun x ≠ 0 ∨ χ₂.toFun x ≠ 0 := by
            by_contra h_both
            push Not at h_both
            rw [h_both.1, h_both.2] at hx_prop
            rw [sub_self] at hx_prop
            exact hx_prop rfl
          simp only [mem_union, Function.mem_support, ne_eq]
          exact h_not_zero
        _ = tsupport (fun x => χ₁.toFun x) ∪ tsupport (fun x => χ₂.toFun x) := by
          rw [closure_union]
          rfl
        _ ⊆ (Ω : Set E) := by
          apply union_subset
          · exact χ₁.tsupport_subset'
          · exact χ₂.tsupport_subset'
    intro x hx
    simp only [mem_sdiff]
    refine ⟨h_subset_Ω hx, ?_⟩
    intro hx_supp
    have h_in_union := h_closure hx
    simp only [mem_union, mem_compl_iff] at h_in_union
    cases h_in_union with
    | inl h1 => exact h1 (hV₁ hx_supp)
    | inr h2 => exact h2 (hV₂ hx_supp)
  exact sub_eq_zero.mp h_eq

omit [FiniteDimensional ℝ E] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] in
lemma applySmooth_congr (T : 𝓓'(Ω, F)) (hT : HasCompactSupport Ω T)
    (f g : E → ℝ) (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g)
    (h_eq : ∀ x, f x = g x)
    (V : Opens E) (hV : Distribution.support Ω T ⊆ (V : Set E))
    (χ : 𝓓(Ω, ℝ)) (hχ_one : ∀ x ∈ (V : Set E), χ x = 1) :
    applySmooth Ω T hT f hf V hV χ hχ_one = applySmooth Ω T hT g hg V hV χ hχ_one := by
  dsimp [applySmooth]
  congr 1
  ext x
  dsimp [applySmoothFun]
  rw [h_eq x]

omit [FiniteDimensional ℝ E] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] in
lemma applySmooth_zero (T : 𝓓'(Ω, F)) (hT : HasCompactSupport Ω T)
    (V : Opens E) (hV : Distribution.support Ω T ⊆ (V : Set E))
    (χ : 𝓓(Ω, ℝ)) (hχ_one : ∀ x ∈ (V : Set E), χ x = 1) :
    applySmooth Ω T hT (fun _ => 0) contDiff_const V hV χ hχ_one = 0 := by
  dsimp [applySmooth]
  have h_zero : applySmoothFun Ω T hT (fun _ => 0) contDiff_const V hV χ hχ_one = 0 := by
    ext x
    dsimp [applySmoothFun]
    exact mul_zero (χ.toFun x)
  rw [h_zero]
  exact map_zero T

omit [FiniteDimensional ℝ E] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] in
lemma applySmooth_add (T : 𝓓'(Ω, F)) (hT : HasCompactSupport Ω T)
    (f g : E → ℝ) (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g)
    (V : Opens E) (hV : Distribution.support Ω T ⊆ (V : Set E))
    (χ : 𝓓(Ω, ℝ)) (hχ_one : ∀ x ∈ (V : Set E), χ x = 1) :
    applySmooth Ω T hT (fun x => f x + g x) (hf.add hg) V hV χ hχ_one =
      applySmooth Ω T hT f hf V hV χ hχ_one + applySmooth Ω T hT g hg V hV χ hχ_one := by
  dsimp [applySmooth]
  have h_add : applySmoothFun Ω T hT (fun x => f x + g x) (hf.add hg) V hV χ hχ_one =
      applySmoothFun Ω T hT f hf V hV χ hχ_one + applySmoothFun Ω T hT g hg V hV χ hχ_one := by
    ext x
    dsimp [applySmoothFun]
    exact mul_add (χ.toFun x) (f x) (g x)
  rw [h_add]
  exact map_add T _ _

omit [FiniteDimensional ℝ E] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] in
lemma applySmooth_sub (T : 𝓓'(Ω, F)) (hT : HasCompactSupport Ω T)
    (f g : E → ℝ) (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g)
    (V : Opens E) (hV : Distribution.support Ω T ⊆ (V : Set E))
    (χ : 𝓓(Ω, ℝ)) (hχ_one : ∀ x ∈ (V : Set E), χ x = 1) :
    applySmooth Ω T hT (fun x => f x - g x) (hf.sub hg) V hV χ hχ_one =
      applySmooth Ω T hT f hf V hV χ hχ_one - applySmooth Ω T hT g hg V hV χ hχ_one := by
  dsimp [applySmooth]
  have h_sub : applySmoothFun Ω T hT (fun x => f x - g x) (hf.sub hg) V hV χ hχ_one =
      applySmoothFun Ω T hT f hf V hV χ hχ_one - applySmoothFun Ω T hT g hg V hV χ hχ_one := by
    ext x
    dsimp [applySmoothFun]
    exact mul_sub (χ.toFun x) (f x) (g x)
  rw [h_sub]
  exact map_sub T _ _

omit [FiniteDimensional ℝ E] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] in
lemma applySmooth_smul (T : 𝓓'(Ω, F)) (hT : HasCompactSupport Ω T)
    (c : ℝ) (f : E → ℝ) (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (V : Opens E) (hV : Distribution.support Ω T ⊆ (V : Set E))
    (χ : 𝓓(Ω, ℝ)) (hχ_one : ∀ x ∈ (V : Set E), χ x = 1) :
    applySmooth Ω T hT (fun x => c * f x) (contDiff_const.mul hf) V hV χ hχ_one =
      c • applySmooth Ω T hT f hf V hV χ hχ_one := by
  dsimp [applySmooth]
  have h_smul : applySmoothFun Ω T hT (fun x => c * f x) (contDiff_const.mul hf) V hV χ hχ_one =
      c • applySmoothFun Ω T hT f hf V hV χ hχ_one := by
    ext x
    dsimp [applySmoothFun]
    change χ.toFun x * (c * f x) = c * (χ.toFun x * f x)
    ring
  rw [h_smul]
  exact map_smul T c _

omit [FiniteDimensional ℝ E] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] in
lemma applySmooth_sum {ι : Type*} (s : Finset ι)
    (T : 𝓓'(Ω, F)) (hT : HasCompactSupport Ω T)
    (f : ι → E → ℝ) (hf : ∀ i, ContDiff ℝ (↑(⊤ : ℕ∞)) (f i))
    (hsum : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => ∑ i ∈ s, f i x))
    (V : Opens E) (hV : Distribution.support Ω T ⊆ (V : Set E))
    (χ : 𝓓(Ω, ℝ)) (hχ_one : ∀ x ∈ (V : Set E), χ x = 1) :
    applySmooth Ω T hT (fun x => ∑ i ∈ s, f i x) hsum V hV χ hχ_one =
      ∑ i ∈ s, applySmooth Ω T hT (f i) (hf i) V hV χ hχ_one := by
  dsimp [applySmooth]
  have h_sum_fun : applySmoothFun Ω T hT (fun x => ∑ i ∈ s, f i x) hsum V hV χ hχ_one =
      ∑ i ∈ s, applySmoothFun Ω T hT (f i) (hf i) V hV χ hχ_one := by
    ext x
    dsimp [applySmoothFun]
    rw [Finset.mul_sum]
    exact (_root_.sum_apply s (fun i => applySmoothFun Ω T hT (f i) (hf i) V hV χ hχ_one) x).symm
  rw [h_sum_fun]
  exact map_sum T (fun i => applySmoothFun Ω T hT (f i) (hf i) V hV χ hχ_one) s

variable {n : ℕ} (V_plus : Set (Fin n → ℝ)) (Ω_n : Opens (Fin n → ℝ))

noncomputable def boundaryIntegral (f : (Fin n → ℂ) → ℂ) (φ : 𝓓(Ω_n, ℝ)) (y : Fin n → ℝ) : ℂ :=
  ∫ (x : Fin n → ℝ), f (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I) * (φ x : ℂ)

def HasBoundaryValue (f : (Fin n → ℂ) → ℂ) (V : Set (Fin n → ℝ)) (T : 𝓓'(Ω_n, ℂ)) : Prop :=
  ∀ φ : 𝓓(Ω_n, ℝ), Filter.Tendsto (boundaryIntegral Ω_n f φ) (nhdsWithin 0 V) (nhds (T φ))

lemma boundary_limit_exists (f : (Fin n → ℂ) → ℂ) (T : 𝓓'(Ω_n, ℂ))
    (h_bval : HasBoundaryValue Ω_n f V_plus T) (φ : 𝓓(Ω_n, ℝ)) :
    ∃ (c : ℂ), Filter.Tendsto (boundaryIntegral Ω_n f φ) (nhdsWithin 0 V_plus) (nhds c) :=
  ⟨T φ, h_bval φ⟩

noncomputable def BoundaryValueDistribution
    (f : (Fin n → ℂ) → ℂ)
    (h_bval : ∃ T : 𝓓'(Ω_n, ℂ), HasBoundaryValue Ω_n f V_plus T) : 𝓓'(Ω_n, ℂ) :=
  Classical.choose h_bval

lemma boundaryValueDistribution_spec
    (f : (Fin n → ℂ) → ℂ)
    (h_bval : ∃ T : 𝓓'(Ω_n, ℂ), HasBoundaryValue Ω_n f V_plus T) :
    HasBoundaryValue Ω_n f V_plus (BoundaryValueDistribution V_plus Ω_n f h_bval) :=
  Classical.choose_spec h_bval

lemma tendsto_boundaryIntegral_of_dominated
    (f : (Fin n → ℂ) → ℂ)
    (f₀ : (Fin n → ℝ) → ℂ)
    (φ : 𝓓(Ω_n, ℝ))
    (bound : (Fin n → ℝ) → ℝ)
    (h_bound_integrable : Integrable bound volume)
    (h_f_meas : ∀ᶠ y in nhdsWithin 0 V_plus,
      AEStronglyMeasurable
        (fun x => f (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I) * (φ x : ℂ)) volume)
    (h_bound : ∀ᶠ y in nhdsWithin 0 V_plus, ∀ᵐ x ∂volume,
      ‖f (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I) * (φ x : ℂ)‖ ≤ bound x)
    (h_tendsto : ∀ᵐ x ∂volume,
      Filter.Tendsto (fun y => f (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I) * (φ x : ℂ))
        (nhdsWithin 0 V_plus) (nhds (f₀ x * (φ x : ℂ)))) :
    Filter.Tendsto (boundaryIntegral Ω_n f φ) (nhdsWithin 0 V_plus)
      (nhds (∫ x, f₀ x * (φ x : ℂ))) :=
  tendsto_integral_boundary V_plus
    (fun y x => f (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I) * (φ x : ℂ))
    (fun x => f₀ x * (φ x : ℂ))
    bound h_bound_integrable h_f_meas h_bound h_tendsto

lemma distribution_compact_bound
    (T : 𝓓'(Ω_n, ℂ)) (K : Compacts (Fin n → ℝ)) (hK : (K : Set (Fin n → ℝ)) ⊆ Ω_n) :
    ∃ (s : Finset ℕ) (C : ℝ≥0), ∀ (f : 𝓓_{K}(Fin n → ℝ, ℝ)),
      ‖T (TestFunction.ofSupportedIn hK f)‖ ≤
        (C : ℝ) * (s.sup (ContDiffMapSupportedIn.seminorm ℝ (Fin n → ℝ) ℝ ⊤ K) f) := by
  let TK : 𝓓_{K}(Fin n → ℝ, ℝ) →L[ℝ] ℂ :=
    (T : 𝓓(Ω_n, ℝ) →L[ℝ] ℂ).comp (TestFunction.ofSupportedInCLM ℝ hK)
  let q : Seminorm ℝ 𝓓_{K}(Fin n → ℝ, ℝ) :=
    (normSeminorm ℝ ℂ).comp TK.toLinearMap
  have hq_cont : Continuous q := by
    dsimp [q]
    exact continuous_norm.comp TK.continuous
  have hp := ContDiffMapSupportedIn.withSeminorms ℝ (Fin n → ℝ) ℝ (⊤ : ℕ∞) K
  rcases Seminorm.bound_of_continuous hp q hq_cont with ⟨s, C, _, h_le⟩
  refine ⟨s, C, ?_⟩
  intro f
  have h_eval := h_le f
  dsimp [q] at h_eval
  exact h_eval

lemma distribution_iteratedFDeriv_bound
    (T : 𝓓'(Ω_n, ℂ)) (K : Compacts (Fin n → ℝ)) (hK : (K : Set (Fin n → ℝ)) ⊆ Ω_n) :
    ∃ (s : Finset ℕ) (C : ℝ≥0), ∀ (f : 𝓓_{K}(Fin n → ℝ, ℝ)) (B : ℝ) (_ : 0 ≤ B),
      (∀ i ∈ s, ∀ x ∈ K, ‖iteratedFDeriv ℝ i (⇑f) x‖ ≤ B) →
      ‖T (TestFunction.ofSupportedIn hK f)‖ ≤ (C : ℝ) * B := by
  rcases distribution_compact_bound Ω_n T K hK with ⟨s, C, h_bound⟩
  refine ⟨s, C, ?_⟩
  intro f B hB h_deriv_bound
  have h_sup : (s.sup (ContDiffMapSupportedIn.seminorm ℝ (Fin n → ℝ) ℝ ⊤ K)) f ≤ B := by
    rw [Seminorm.finset_sup_apply]
    have h_le_nn : (s.sup fun i => ⟨(ContDiffMapSupportedIn.seminorm ℝ (Fin n → ℝ) ℝ ⊤ K i) f,
        apply_nonneg (ContDiffMapSupportedIn.seminorm ℝ (Fin n → ℝ) ℝ ⊤ K i) f⟩) ≤
          (⟨B, hB⟩ : ℝ≥0) := by
      apply Finset.sup_le
      intro i hi
      have h_real : (ContDiffMapSupportedIn.seminorm ℝ (Fin n → ℝ) ℝ ⊤ K i) f ≤ B := by
        rw [ContDiffMapSupportedIn.seminorm_le_iff (𝕜 := ℝ) hB i f]
        intro _ x hx
        exact h_deriv_bound i hi x hx
      exact h_real
    exact h_le_nn
  have h_mul := mul_le_mul_of_nonneg_left h_sup (NNReal.coe_nonneg C)
  exact (h_bound f).trans h_mul

def applySmoothSupportedIn (T : 𝓓'(Ω_n, ℂ)) (_ : HasCompactSupport Ω_n T)
    (ψ : (Fin n → ℝ) → ℝ) (hψ : ContDiff ℝ (↑(⊤ : ℕ∞)) ψ)
    (V : Opens (Fin n → ℝ)) (_ : Distribution.support Ω_n T ⊆ (V : Set (Fin n → ℝ)))
    (χ : 𝓓(Ω_n, ℝ)) (_ : ∀ x ∈ (V : Set (Fin n → ℝ)), χ x = 1) :
    let K : Compacts (Fin n → ℝ) := ⟨tsupport χ, χ.hasCompactSupport'⟩
    𝓓_{K}(Fin n → ℝ, ℝ) where
  toFun := fun x => χ.toFun x * ψ x
  contDiff' := ContDiff.mul χ.contDiff' hψ
  zero_on_compl' := by
    intro x hx
    have h_not_tsupp : x ∉ tsupport χ := hx
    have h_zero : χ.toFun x = 0 := by
      by_contra h_ne
      exact h_not_tsupp (subset_tsupport χ h_ne)
    dsimp only
    rw [h_zero, zero_mul]
    rfl

lemma ofSupportedIn_applySmoothSupportedIn (T : 𝓓'(Ω_n, ℂ)) (hT : HasCompactSupport Ω_n T)
    (ψ : (Fin n → ℝ) → ℝ) (hψ : ContDiff ℝ (↑(⊤ : ℕ∞)) ψ)
    (V : Opens (Fin n → ℝ)) (hV : Distribution.support Ω_n T ⊆ (V : Set (Fin n → ℝ)))
    (χ : 𝓓(Ω_n, ℝ)) (hχ_one : ∀ x ∈ (V : Set (Fin n → ℝ)), χ x = 1) :
    let K : Compacts (Fin n → ℝ) := ⟨tsupport χ, χ.hasCompactSupport'⟩
    TestFunction.ofSupportedIn (K := K) χ.tsupport_subset'
      (applySmoothSupportedIn Ω_n T hT ψ hψ V hV χ hχ_one) =
      applySmoothFun Ω_n T hT ψ hψ V hV χ hχ_one := by
  ext x
  rfl

lemma applySmooth_bound
    (T : 𝓓'(Ω_n, ℂ)) (hT : HasCompactSupport Ω_n T)
    (V : Opens (Fin n → ℝ)) (hV : Distribution.support Ω_n T ⊆ (V : Set (Fin n → ℝ)))
    (χ : 𝓓(Ω_n, ℝ)) (hχ_one : ∀ x ∈ (V : Set (Fin n → ℝ)), χ x = 1) :
    let K : Compacts (Fin n → ℝ) := ⟨tsupport χ, χ.hasCompactSupport'⟩
    ∃ (s : Finset ℕ) (C : ℝ≥0), ∀ (ψ : (Fin n → ℝ) → ℝ) (hψ : ContDiff ℝ (↑(⊤ : ℕ∞)) ψ)
      (B : ℝ) (_ : 0 ≤ B),
      (∀ i ∈ s, ∀ x ∈ (K : Set (Fin n → ℝ)),
        ‖iteratedFDeriv ℝ i (fun y => χ.toFun y * ψ y) x‖ ≤ B) →
      ‖applySmooth Ω_n T hT ψ hψ V hV χ hχ_one‖ ≤ (C : ℝ) * B := by
  let K : Compacts (Fin n → ℝ) := ⟨tsupport χ, χ.hasCompactSupport'⟩
  rcases distribution_iteratedFDeriv_bound Ω_n T K χ.tsupport_subset' with ⟨s, C, h_bound⟩
  refine ⟨s, C, ?_⟩
  intro ψ hψ B hB h_deriv
  dsimp [applySmooth]
  rw [← ofSupportedIn_applySmoothSupportedIn Ω_n T hT ψ hψ V hV χ hχ_one]
  exact h_bound (applySmoothSupportedIn Ω_n T hT ψ hψ V hV χ hχ_one) B hB h_deriv

noncomputable def applySmoothComplex (T : 𝓓'(Ω_n, ℂ)) (hT : HasCompactSupport Ω_n T)
    (ψ : (Fin n → ℝ) → ℂ) (hψ_re : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (ψ x).re))
    (hψ_im : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (ψ x).im))
    (V : Opens (Fin n → ℝ)) (hV : Distribution.support Ω_n T ⊆ (V : Set (Fin n → ℝ)))
    (χ : 𝓓(Ω_n, ℝ)) (hχ_one : ∀ x ∈ (V : Set (Fin n → ℝ)), χ x = 1) : ℂ :=
  let ψ_re := fun x => (ψ x).re
  let ψ_im := fun x => (ψ x).im
  applySmooth Ω_n T hT ψ_re hψ_re V hV χ hχ_one +
    Complex.I * applySmooth Ω_n T hT ψ_im hψ_im V hV χ hχ_one

lemma applySmoothComplex_bound
    (T : 𝓓'(Ω_n, ℂ)) (hT : HasCompactSupport Ω_n T)
    (V : Opens (Fin n → ℝ)) (hV : Distribution.support Ω_n T ⊆ (V : Set (Fin n → ℝ)))
    (χ : 𝓓(Ω_n, ℝ)) (hχ_one : ∀ x ∈ (V : Set (Fin n → ℝ)), χ x = 1) :
    let K : Compacts (Fin n → ℝ) := ⟨tsupport χ, χ.hasCompactSupport'⟩
    ∃ (s : Finset ℕ) (C : ℝ≥0), ∀ (ψ : (Fin n → ℝ) → ℂ)
      (hψ_re : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (ψ x).re))
      (hψ_im : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (ψ x).im))
      (B : ℝ) (_ : 0 ≤ B),
      (∀ i ∈ s, ∀ x ∈ (K : Set (Fin n → ℝ)),
        ‖iteratedFDeriv ℝ i (fun y => χ.toFun y * (ψ y).re) x‖ ≤ B) →
      (∀ i ∈ s, ∀ x ∈ (K : Set (Fin n → ℝ)),
        ‖iteratedFDeriv ℝ i (fun y => χ.toFun y * (ψ y).im) x‖ ≤ B) →
      ‖applySmoothComplex Ω_n T hT ψ hψ_re hψ_im V hV χ hχ_one‖ ≤ (2 * (C : ℝ)) * B := by
  rcases applySmooth_bound Ω_n T hT V hV χ hχ_one with ⟨s, C, h_bound⟩
  refine ⟨s, C, ?_⟩
  intro ψ hψ_re hψ_im B hB h_re h_im
  dsimp [applySmoothComplex]
  have h_norm := norm_add_le (applySmooth Ω_n T hT (fun x => (ψ x).re) hψ_re V hV χ hχ_one)
    (Complex.I * applySmooth Ω_n T hT (fun x => (ψ x).im) hψ_im V hV χ hχ_one)
  have h_I : ‖Complex.I * applySmooth Ω_n T hT (fun x => (ψ x).im) hψ_im V hV χ hχ_one‖ =
      ‖applySmooth Ω_n T hT (fun x => (ψ x).im) hψ_im V hV χ hχ_one‖ := by
    rw [norm_mul, Complex.norm_I, one_mul]
  rw [h_I] at h_norm
  have h1 := h_bound (fun x => (ψ x).re) hψ_re B hB h_re
  have h2 := h_bound (fun x => (ψ x).im) hψ_im B hB h_im
  linarith

lemma applySmoothComplex_add (T : 𝓓'(Ω_n, ℂ)) (hT : HasCompactSupport Ω_n T)
    (V : Opens (Fin n → ℝ)) (hV : Distribution.support Ω_n T ⊆ (V : Set (Fin n → ℝ)))
    (χ : 𝓓(Ω_n, ℝ)) (hχ_one : ∀ x ∈ (V : Set (Fin n → ℝ)), χ x = 1)
    (f g : (Fin n → ℝ) → ℂ)
    (hf_re : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (f x).re))
    (hf_im : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (f x).im))
    (hg_re : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (g x).re))
    (hg_im : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (g x).im)) :
    applySmoothComplex Ω_n T hT (fun x => f x + g x) (hf_re.add hg_re) (hf_im.add hg_im)
      V hV χ hχ_one =
      applySmoothComplex Ω_n T hT f hf_re hf_im V hV χ hχ_one +
      applySmoothComplex Ω_n T hT g hg_re hg_im V hV χ hχ_one := by
  dsimp [applySmoothComplex]
  rw [applySmooth_add Ω_n T hT (fun x => (f x).re) (fun x => (g x).re) hf_re hg_re V hV χ hχ_one]
  rw [applySmooth_add Ω_n T hT (fun x => (f x).im) (fun x => (g x).im) hf_im hg_im V hV χ hχ_one]
  ring

lemma applySmoothComplex_sub (T : 𝓓'(Ω_n, ℂ)) (hT : HasCompactSupport Ω_n T)
    (V : Opens (Fin n → ℝ)) (hV : Distribution.support Ω_n T ⊆ (V : Set (Fin n → ℝ)))
    (χ : 𝓓(Ω_n, ℝ)) (hχ_one : ∀ x ∈ (V : Set (Fin n → ℝ)), χ x = 1)
    (f g : (Fin n → ℝ) → ℂ)
    (hf_re : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (f x).re))
    (hf_im : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (f x).im))
    (hg_re : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (g x).re))
    (hg_im : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (g x).im)) :
    applySmoothComplex Ω_n T hT (fun x => f x - g x) (hf_re.sub hg_re) (hf_im.sub hg_im)
      V hV χ hχ_one =
      applySmoothComplex Ω_n T hT f hf_re hf_im V hV χ hχ_one -
      applySmoothComplex Ω_n T hT g hg_re hg_im V hV χ hχ_one := by
  dsimp [applySmoothComplex]
  rw [applySmooth_sub Ω_n T hT (fun x => (f x).re) (fun x => (g x).re) hf_re hg_re V hV χ hχ_one]
  rw [applySmooth_sub Ω_n T hT (fun x => (f x).im) (fun x => (g x).im) hf_im hg_im V hV χ hχ_one]
  ring

lemma applySmoothComplex_sub_sub
    (T : 𝓓'(Ω_n, ℂ)) (hT : HasCompactSupport Ω_n T)
    (V : Opens (Fin n → ℝ)) (hV : Distribution.support Ω_n T ⊆ (V : Set (Fin n → ℝ)))
    (χ : 𝓓(Ω_n, ℝ)) (hχ_one : ∀ x ∈ (V : Set (Fin n → ℝ)), χ x = 1)
    (f₁ f₂ f₃ : (Fin n → ℝ) → ℂ)
    (hf₁_re : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (f₁ x).re))
    (hf₁_im : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (f₁ x).im))
    (hf₂_re : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (f₂ x).re))
    (hf₂_im : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (f₂ x).im))
    (hf₃_re : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (f₃ x).re))
    (hf₃_im : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (f₃ x).im)) :
    applySmoothComplex Ω_n T hT (fun x => f₁ x - f₂ x - f₃ x)
      (((hf₁_re.sub hf₂_re).sub hf₃_re)) (((hf₁_im.sub hf₂_im).sub hf₃_im)) V hV χ hχ_one =
      applySmoothComplex Ω_n T hT f₁ hf₁_re hf₁_im V hV χ hχ_one -
      applySmoothComplex Ω_n T hT f₂ hf₂_re hf₂_im V hV χ hχ_one -
      applySmoothComplex Ω_n T hT f₃ hf₃_re hf₃_im V hV χ hχ_one := by
  have h1 := applySmoothComplex_sub Ω_n T hT V hV χ hχ_one (fun x => f₁ x - f₂ x) f₃
    (hf₁_re.sub hf₂_re) (hf₁_im.sub hf₂_im) hf₃_re hf₃_im
  have h2 := applySmoothComplex_sub Ω_n T hT V hV χ hχ_one f₁ f₂ hf₁_re hf₁_im hf₂_re hf₂_im
  rw [h1, h2]

lemma applySmoothComplex_const_mul
    (T : 𝓓'(Ω_n, ℂ)) (hT : HasCompactSupport Ω_n T)
    (V : Opens (Fin n → ℝ)) (hV : Distribution.support Ω_n T ⊆ (V : Set (Fin n → ℝ)))
    (χ : 𝓓(Ω_n, ℝ)) (hχ_one : ∀ x ∈ (V : Set (Fin n → ℝ)), χ x = 1)
    (c : ℂ) (ψ : (Fin n → ℝ) → ℂ)
    (hψ_re : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (ψ x).re))
    (hψ_im : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (ψ x).im))
    (hcψ_re : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (c * ψ x).re))
    (hcψ_im : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (c * ψ x).im)) :
    applySmoothComplex Ω_n T hT (fun x => c * ψ x) hcψ_re hcψ_im V hV χ hχ_one =
    c * applySmoothComplex Ω_n T hT ψ hψ_re hψ_im V hV χ hχ_one := by
  dsimp [applySmoothComplex]
  have h_re_diff : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => c.re * (ψ x).re - c.im * (ψ x).im) :=
    (contDiff_const.mul hψ_re).sub (contDiff_const.mul hψ_im)
  have h_im_diff : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => c.re * (ψ x).im + c.im * (ψ x).re) :=
    (contDiff_const.mul hψ_im).add (contDiff_const.mul hψ_re)
  have h1 : applySmooth Ω_n T hT (fun x => (c * ψ x).re) hcψ_re V hV χ hχ_one =
      applySmooth Ω_n T hT (fun x => c.re * (ψ x).re - c.im * (ψ x).im)
        h_re_diff V hV χ hχ_one := by
    apply applySmooth_congr Ω_n T hT _ _ _ _ (fun x => by simp [Complex.mul_re])
  have h2 : applySmooth Ω_n T hT (fun x => (c * ψ x).im) hcψ_im V hV χ hχ_one =
      applySmooth Ω_n T hT (fun x => c.re * (ψ x).im + c.im * (ψ x).re)
        h_im_diff V hV χ hχ_one := by
    apply applySmooth_congr Ω_n T hT _ _ _ _ (fun x => by simp [Complex.mul_im])
  rw [h1, h2]
  rw [applySmooth_sub Ω_n T hT _ _ (contDiff_const.mul hψ_re) (contDiff_const.mul hψ_im)
    V hV χ hχ_one]
  rw [applySmooth_add Ω_n T hT _ _ (contDiff_const.mul hψ_im) (contDiff_const.mul hψ_re)
    V hV χ hχ_one]
  rw [applySmooth_smul Ω_n T hT c.re _ hψ_re V hV χ hχ_one]
  rw [applySmooth_smul Ω_n T hT c.im _ hψ_im V hV χ hχ_one]
  rw [applySmooth_smul Ω_n T hT c.re _ hψ_im V hV χ hχ_one]
  rw [applySmooth_smul Ω_n T hT c.im _ hψ_re V hV χ hχ_one]
  simp only [Complex.real_smul]
  conv_rhs =>
    rw [show c = (c.re : ℂ) + (c.im : ℂ) * Complex.I from (Complex.re_add_im c).symm]
  have h_I_sq := Complex.I_sq
  linear_combination
    -((c.im : ℂ) * applySmooth Ω_n T hT (fun x => (ψ x).im) hψ_im V hV χ hχ_one) * h_I_sq

lemma applySmoothComplex_zero
    (T : 𝓓'(Ω_n, ℂ)) (hT : HasCompactSupport Ω_n T)
    (V : Opens (Fin n → ℝ)) (hV : Distribution.support Ω_n T ⊆ (V : Set (Fin n → ℝ)))
    (χ : 𝓓(Ω_n, ℝ)) (hχ_one : ∀ x ∈ (V : Set (Fin n → ℝ)), χ x = 1) :
    applySmoothComplex Ω_n T hT (fun _ => 0) contDiff_const contDiff_const V hV χ hχ_one = 0 := by
  dsimp [applySmoothComplex]
  have h := applySmooth_zero Ω_n T hT V hV χ hχ_one
  rw [h]
  simp

open Finset

lemma applySmoothComplex_sum {ι : Type*} (s : Finset ι)
    (T : 𝓓'(Ω_n, ℂ)) (hT : HasCompactSupport Ω_n T)
    (f : ι → (Fin n → ℝ) → ℂ)
    (hf_re : ∀ i, ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (f i x).re))
    (hf_im : ∀ i, ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (f i x).im))
    (hsum_re : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (∑ i ∈ s, f i x).re))
    (hsum_im : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (∑ i ∈ s, f i x).im))
    (V : Opens (Fin n → ℝ)) (hV : Distribution.support Ω_n T ⊆ (V : Set (Fin n → ℝ)))
    (χ : 𝓓(Ω_n, ℝ)) (hχ_one : ∀ x ∈ (V : Set (Fin n → ℝ)), χ x = 1) :
    applySmoothComplex Ω_n T hT (fun x => ∑ i ∈ s, f i x) hsum_re hsum_im V hV χ hχ_one =
      ∑ i ∈ s, applySmoothComplex Ω_n T hT (f i) (hf_re i) (hf_im i) V hV χ hχ_one := by
  dsimp [applySmoothComplex]
  have h_re_eq : (fun x => (∑ i ∈ s, f i x).re) = fun x => ∑ i ∈ s, (f i x).re := by
    ext x
    simp only [Complex.re_sum]
  have h_im_eq : (fun x => (∑ i ∈ s, f i x).im) = fun x => ∑ i ∈ s, (f i x).im := by
    ext x
    simp only [Complex.im_sum]
  have h_re_diff : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => ∑ i ∈ s, (f i x).re) := by
    apply ContDiff.sum
    intro i _
    exact hf_re i
  have h_im_diff : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => ∑ i ∈ s, (f i x).im) := by
    apply ContDiff.sum
    intro i _
    exact hf_im i
  have h1 : applySmooth Ω_n T hT (fun x => (∑ i ∈ s, f i x).re) hsum_re V hV χ hχ_one =
      ∑ i ∈ s, applySmooth Ω_n T hT (fun x => (f i x).re) (hf_re i) V hV χ hχ_one := by
    rw [applySmooth_congr Ω_n T hT _ _ hsum_re h_re_diff (congrFun h_re_eq) V hV χ hχ_one]
    exact applySmooth_sum Ω_n s T hT (fun i x => (f i x).re) hf_re h_re_diff V hV χ hχ_one
  have h2 : applySmooth Ω_n T hT (fun x => (∑ i ∈ s, f i x).im) hsum_im V hV χ hχ_one =
      ∑ i ∈ s, applySmooth Ω_n T hT (fun x => (f i x).im) (hf_im i) V hV χ hχ_one := by
    rw [applySmooth_congr Ω_n T hT _ _ hsum_im h_im_diff (congrFun h_im_eq) V hV χ hχ_one]
    exact applySmooth_sum Ω_n s T hT (fun i x => (f i x).im) hf_im h_im_diff V hV χ hχ_one
  rw [h1, h2]
  rw [mul_sum, ← sum_add_distrib]

lemma applySmoothComplex_congr (T : 𝓓'(Ω_n, ℂ)) (hT : HasCompactSupport Ω_n T)
    (f g : (Fin n → ℝ) → ℂ)
    (hf_re : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (f x).re))
    (hf_im : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (f x).im))
    (hg_re : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (g x).re))
    (hg_im : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (g x).im))
    (h_eq : ∀ x, f x = g x)
    (V : Opens (Fin n → ℝ)) (hV : Distribution.support Ω_n T ⊆ (V : Set (Fin n → ℝ)))
    (χ : 𝓓(Ω_n, ℝ)) (hχ_one : ∀ x ∈ (V : Set (Fin n → ℝ)), χ x = 1) :
    applySmoothComplex Ω_n T hT f hf_re hf_im V hV χ hχ_one =
      applySmoothComplex Ω_n T hT g hg_re hg_im V hV χ hχ_one := by
  dsimp [applySmoothComplex]
  have h_re : applySmooth Ω_n T hT (fun x => (f x).re) hf_re V hV χ hχ_one =
      applySmooth Ω_n T hT (fun x => (g x).re) hg_re V hV χ hχ_one :=
    applySmooth_congr Ω_n T hT _ _ hf_re hg_re (fun x => by rw [h_eq x]) V hV χ hχ_one
  have h_im : applySmooth Ω_n T hT (fun x => (f x).im) hf_im V hV χ hχ_one =
      applySmooth Ω_n T hT (fun x => (g x).im) hg_im V hV χ hχ_one :=
    applySmooth_congr Ω_n T hT _ _ hf_im hg_im (fun x => by rw [h_eq x]) V hV χ hχ_one
  rw [h_re, h_im]

lemma x_i_smooth (i : Fin n) : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun (x : Fin n → ℝ) => (x i : ℂ)) := by
  have h1 : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun (x : Fin n → ℝ) => x i) :=
    contDiff_pi.mp contDiff_id i
  have h2 : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun (y : ℝ) => (y : ℂ)) :=
    ContinuousLinearMap.contDiff Complex.ofRealCLM
  exact h2.comp h1

lemma exp_izx_smooth (z : Fin n → ℂ) :
    ContDiff ℝ (↑(⊤ : ℕ∞))
      (fun (x : Fin n → ℝ) => Complex.exp (-Complex.I * (∑ i, z i * (x i : ℂ)))) := by
  apply ContDiff.cexp
  apply ContDiff.mul
  · exact contDiff_const
  · apply ContDiff.sum
    intro i _
    apply ContDiff.mul
    · exact contDiff_const
    · exact x_i_smooth i

lemma exp_izx_re_smooth (z : Fin n → ℂ) :
    ContDiff ℝ (↑(⊤ : ℕ∞))
      (fun (x : Fin n → ℝ) => (Complex.exp (-Complex.I * (∑ i, z i * (x i : ℂ)))).re) := by
  exact Complex.reCLM.contDiff.comp (exp_izx_smooth z)

lemma exp_izx_im_smooth (z : Fin n → ℂ) :
    ContDiff ℝ (↑(⊤ : ℕ∞))
      (fun (x : Fin n → ℝ) => (Complex.exp (-Complex.I * (∑ i, z i * (x i : ℂ)))).im) := by
  exact Complex.imCLM.contDiff.comp (exp_izx_smooth z)

lemma x_mul_exp_izx_smooth (z : Fin n → ℂ) (k : Fin n) :
    ContDiff ℝ (↑(⊤ : ℕ∞))
      (fun (x : Fin n → ℝ) => (x k : ℂ) * Complex.exp (-Complex.I * (∑ i, z i * (x i : ℂ)))) :=
  (x_i_smooth k).mul (exp_izx_smooth z)

lemma x_mul_exp_izx_re_smooth (z : Fin n → ℂ) (k : Fin n) :
    ContDiff ℝ (↑(⊤ : ℕ∞))
      (fun (x : Fin n → ℝ) => ((x k : ℂ) * Complex.exp (-Complex.I * (∑ i, z i * (x i : ℂ)))).re) :=
  Complex.reCLM.contDiff.comp (x_mul_exp_izx_smooth z k)

lemma x_mul_exp_izx_im_smooth (z : Fin n → ℂ) (k : Fin n) :
    ContDiff ℝ (↑(⊤ : ℕ∞))
      (fun (x : Fin n → ℝ) => ((x k : ℂ) * Complex.exp (-Complex.I * (∑ i, z i * (x i : ℂ)))).im) :=
  Complex.imCLM.contDiff.comp (x_mul_exp_izx_smooth z k)

noncomputable def FourierLaplaceDeriv (T : 𝓓'(Ω_n, ℂ)) (hT : HasCompactSupport Ω_n T)
    (V : Opens (Fin n → ℝ)) (hV : Distribution.support Ω_n T ⊆ (V : Set (Fin n → ℝ)))
    (χ : 𝓓(Ω_n, ℝ)) (hχ_one : ∀ x ∈ (V : Set (Fin n → ℝ)), χ x = 1)
    (k : Fin n) (z : Fin n → ℂ) : ℂ :=
  let x_e_izx := fun (x : Fin n → ℝ) =>
    (x k : ℂ) * Complex.exp (-Complex.I * (∑ i, z i * (x i : ℂ)))
  (-Complex.I) * applySmoothComplex Ω_n T hT x_e_izx (x_mul_exp_izx_re_smooth z k)
    (x_mul_exp_izx_im_smooth z k) V hV χ hχ_one

noncomputable def FourierLaplaceTotalDeriv (T : 𝓓'(Ω_n, ℂ)) (hT : HasCompactSupport Ω_n T)
    (V : Opens (Fin n → ℝ)) (hV : Distribution.support Ω_n T ⊆ (V : Set (Fin n → ℝ)))
    (χ : 𝓓(Ω_n, ℝ)) (hχ_one : ∀ x ∈ (V : Set (Fin n → ℝ)), χ x = 1) (z : Fin n → ℂ) :
    (Fin n → ℂ) →L[ℂ] ℂ :=
  ∑ k, (ContinuousLinearMap.proj k).smulRight (FourierLaplaceDeriv Ω_n T hT V hV χ hχ_one k z)

lemma FourierLaplaceTotalDeriv_apply (T : 𝓓'(Ω_n, ℂ)) (hT : HasCompactSupport Ω_n T)
    (V : Opens (Fin n → ℝ)) (hV : Distribution.support Ω_n T ⊆ (V : Set (Fin n → ℝ)))
    (χ : 𝓓(Ω_n, ℝ)) (hχ_one : ∀ x ∈ (V : Set (Fin n → ℝ)), χ x = 1) (z : Fin n → ℂ)
    (h : Fin n → ℂ) :
    FourierLaplaceTotalDeriv Ω_n T hT V hV χ hχ_one z h =
      ∑ k, h k * FourierLaplaceDeriv Ω_n T hT V hV χ hχ_one k z := by
  dsimp [FourierLaplaceTotalDeriv]
  simp only [_root_.sum_apply, smulRight_apply, proj_apply, smul_eq_mul]

noncomputable def FourierLaplaceTransform (T : 𝓓'(Ω_n, ℂ)) (hT : HasCompactSupport Ω_n T)
    (V : Opens (Fin n → ℝ)) (hV : Distribution.support Ω_n T ⊆ (V : Set (Fin n → ℝ)))
    (χ : 𝓓(Ω_n, ℝ)) (hχ_one : ∀ x ∈ (V : Set (Fin n → ℝ)), χ x = 1) (z : Fin n → ℂ) : ℂ :=
  let e_izx := fun (x : Fin n → ℝ) => Complex.exp (-Complex.I * (∑ i, z i * (x i : ℂ)))
  applySmoothComplex Ω_n T hT e_izx (exp_izx_re_smooth z) (exp_izx_im_smooth z) V hV χ hχ_one

lemma fourier_diff_zero (T : 𝓓'(Ω_n, ℂ)) (hT : HasCompactSupport Ω_n T)
    (V : Opens (Fin n → ℝ)) (hV : Distribution.support Ω_n T ⊆ (V : Set (Fin n → ℝ)))
    (χ : 𝓓(Ω_n, ℝ)) (hχ_one : ∀ x ∈ (V : Set (Fin n → ℝ)), χ x = 1)
    (hn : n = 0) :
    Differentiable ℂ (FourierLaplaceTransform Ω_n T hT V hV χ hχ_one) := by
  intro z
  have h_subsingleton : Subsingleton (Fin n → ℂ) := by
    subst hn
    infer_instance
  have h_const : ∀ w : Fin n → ℂ, w = z := fun w => Subsingleton.elim w z
  have h_eq : (FourierLaplaceTransform Ω_n T hT V hV χ hχ_one) =
      fun _ => FourierLaplaceTransform Ω_n T hT V hV χ hχ_one z := by
    ext w
    rw [h_const w]
  rw [h_eq]
  exact differentiableAt_const _

lemma applySmooth_empty_support (T : 𝓓'(Ω_n, ℂ)) (hT : HasCompactSupport Ω_n T)
    (h_supp : Distribution.support Ω_n T = ∅)
    (ψ : (Fin n → ℝ) → ℝ) (hψ : ContDiff ℝ (↑(⊤ : ℕ∞)) ψ)
    (V : Opens (Fin n → ℝ)) (hV : Distribution.support Ω_n T ⊆ (V : Set (Fin n → ℝ)))
    (χ : 𝓓(Ω_n, ℝ)) (hχ_one : ∀ x ∈ (V : Set (Fin n → ℝ)), χ x = 1) :
    applySmooth Ω_n T hT ψ hψ V hV χ hχ_one = 0 := by
  dsimp [applySmooth]
  apply vanishing_on_disjoint_support
  intro x hx
  simp only [h_supp, sdiff_empty]
  exact (applySmoothFun Ω_n T hT ψ hψ V hV χ hχ_one).tsupport_subset' hx

lemma applySmoothComplex_empty_support (T : 𝓓'(Ω_n, ℂ)) (hT : HasCompactSupport Ω_n T)
    (h_supp : Distribution.support Ω_n T = ∅)
    (ψ : (Fin n → ℝ) → ℂ)
    (hψ_re : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (ψ x).re))
    (hψ_im : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (ψ x).im))
    (V : Opens (Fin n → ℝ)) (hV : Distribution.support Ω_n T ⊆ (V : Set (Fin n → ℝ)))
    (χ : 𝓓(Ω_n, ℝ)) (hχ_one : ∀ x ∈ (V : Set (Fin n → ℝ)), χ x = 1) :
    applySmoothComplex Ω_n T hT ψ hψ_re hψ_im V hV χ hχ_one = 0 := by
  dsimp [applySmoothComplex]
  rw [applySmooth_empty_support Ω_n T hT h_supp _ hψ_re V hV χ hχ_one]
  rw [applySmooth_empty_support Ω_n T hT h_supp _ hψ_im V hV χ hχ_one]
  simp

lemma fourier_laplace_empty_support (T : 𝓓'(Ω_n, ℂ)) (hT : HasCompactSupport Ω_n T)
    (h_supp : Distribution.support Ω_n T = ∅)
    (V : Opens (Fin n → ℝ)) (hV : Distribution.support Ω_n T ⊆ (V : Set (Fin n → ℝ)))
    (χ : 𝓓(Ω_n, ℝ)) (hχ_one : ∀ x ∈ (V : Set (Fin n → ℝ)), χ x = 1) (z : Fin n → ℂ) :
    HasFDerivAt (FourierLaplaceTransform Ω_n T hT V hV χ hχ_one)
      (FourierLaplaceTotalDeriv Ω_n T hT V hV χ hχ_one z) z := by
  have h_flt : (FourierLaplaceTransform Ω_n T hT V hV χ hχ_one) = fun _ => 0 := by
    ext w
    dsimp [FourierLaplaceTransform]
    exact applySmoothComplex_empty_support Ω_n T hT h_supp _ _ _ V hV χ hχ_one
  have h_deriv : FourierLaplaceTotalDeriv Ω_n T hT V hV χ hχ_one z = 0 := by
    ext h
    rw [FourierLaplaceTotalDeriv_apply]
    have h_k : ∀ k, FourierLaplaceDeriv Ω_n T hT V hV χ hχ_one k z = 0 := by
      intro k
      dsimp [FourierLaplaceDeriv]
      rw [applySmoothComplex_empty_support Ω_n T hT h_supp _ _ _ V hV χ hχ_one]
      ring
    simp [h_k]
  rw [h_flt, h_deriv]
  exact hasFDerivAt_const (𝕜 := ℂ) 0 z

noncomputable def expTaylorRem (z h : Fin n → ℂ) (x : Fin n → ℝ) : ℂ :=
  Complex.exp (-Complex.I * (∑ i, (z i + h i) * (x i : ℂ))) -
  Complex.exp (-Complex.I * (∑ i, z i * (x i : ℂ))) -
  (∑ k, h k * ((-Complex.I * (x k : ℂ)) * Complex.exp (-Complex.I * (∑ i, z i * (x i : ℂ)))))

lemma expTaylorRem_zero (z : Fin n → ℂ) (x : Fin n → ℝ) :
    expTaylorRem z 0 x = 0 := by
  dsimp [expTaylorRem]
  simp

lemma expTaylorRem_factor (z h : Fin n → ℂ) (x : Fin n → ℝ) :
    expTaylorRem z h x =
      Complex.exp (-Complex.I * (∑ i, z i * (x i : ℂ))) *
        (Complex.exp (-Complex.I * (∑ i, h i * (x i : ℂ))) - 1 -
          (-Complex.I * (∑ i, h i * (x i : ℂ)))) := by
  dsimp [expTaylorRem]
  have h_add : (-Complex.I * (∑ i, (z i + h i) * (x i : ℂ))) =
      (-Complex.I * (∑ i, z i * (x i : ℂ))) + (-Complex.I * (∑ i, h i * (x i : ℂ))) := by
    simp_rw [add_mul, Finset.sum_add_distrib, mul_add]
  rw [h_add, Complex.exp_add]
  have h_sum :
      (∑ k, h k * ((-Complex.I * (x k : ℂ)) *
        Complex.exp (-Complex.I * (∑ i, z i * (x i : ℂ))))) =
      Complex.exp (-Complex.I * (∑ i, z i * (x i : ℂ))) *
        (-Complex.I * (∑ i, h i * (x i : ℂ))) := by
    calc ∑ k, h k * ((-Complex.I * (x k : ℂ)) *
          Complex.exp (-Complex.I * (∑ i, z i * (x i : ℂ))))
      _ = ∑ k, (Complex.exp (-Complex.I * (∑ i, z i * (x i : ℂ))) * -Complex.I) *
            (h k * (x k : ℂ)) := by
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = (Complex.exp (-Complex.I * (∑ i, z i * (x i : ℂ))) * -Complex.I) *
            (∑ k, h k * (x k : ℂ)) := by
        rw [← Finset.mul_sum]
      _ = Complex.exp (-Complex.I * (∑ i, z i * (x i : ℂ))) *
            (-Complex.I * (∑ i, h i * (x i : ℂ))) := by
        ring
  rw [h_sum]
  ring

lemma exp_two_rem (u : ℂ) :
    ‖Complex.exp u - 1 - u‖ ≤ ‖u‖^2 * Real.exp ‖u‖ := by
  have h := Complex.norm_exp_sub_sum_le_norm_mul_exp u 2
  have h_sum : (∑ m ∈ Finset.range 2, u ^ m / (m.factorial : ℂ)) = 1 + u := by
    simp [Finset.sum_range_succ]
  rw [h_sum] at h
  have h_eq : Complex.exp u - (1 + u) = Complex.exp u - 1 - u := by ring
  rw [h_eq] at h
  exact h

lemma expTaylorRem_smooth (z h : Fin n → ℂ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun (x : Fin n → ℝ) => expTaylorRem z h x) := by
  dsimp [expTaylorRem]
  apply ContDiff.sub
  · apply ContDiff.sub
    · exact exp_izx_smooth (z + h)
    · exact exp_izx_smooth z
  · apply ContDiff.sum
    intro k _
    apply ContDiff.mul
    · exact contDiff_const
    · apply ContDiff.mul
      · apply ContDiff.mul
        · exact contDiff_const
        · exact x_i_smooth k
      · exact exp_izx_smooth z

lemma expTaylorRem_re_smooth (z h : Fin n → ℂ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun (x : Fin n → ℝ) => (expTaylorRem z h x).re) :=
  Complex.reCLM.contDiff.comp (expTaylorRem_smooth z h)

lemma expTaylorRem_im_smooth (z h : Fin n → ℂ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun (x : Fin n → ℝ) => (expTaylorRem z h x).im) :=
  Complex.imCLM.contDiff.comp (expTaylorRem_smooth z h)

lemma norm_re_iteratedFDeriv_le (i : ℕ) (f : (Fin n → ℝ) → ℂ)
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (x : Fin n → ℝ) :
    ‖iteratedFDeriv ℝ i (fun y => (f y).re) x‖ ≤ ‖iteratedFDeriv ℝ i f x‖ := by
  have h_comp : (fun y => (f y).re) = Complex.reCLM ∘ f := rfl
  rw [h_comp]
  have h_diff : ContDiffAt ℝ (↑(⊤ : ℕ∞)) f x := hf.contDiffAt
  have h_le : (i : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) :=
    WithTop.coe_le_coe.mpr le_top
  rw [ContinuousLinearMap.iteratedFDeriv_comp_left Complex.reCLM h_diff h_le]
  have h_le :=
    ContinuousLinearMap.norm_compContinuousMultilinearMap_le Complex.reCLM
      (iteratedFDeriv ℝ i f x)
  have h_norm : ‖Complex.reCLM‖ = 1 := Complex.reCLM_norm
  calc ‖Complex.reCLM.compContinuousMultilinearMap (iteratedFDeriv ℝ i f x)‖
    _ ≤ ‖Complex.reCLM‖ * ‖iteratedFDeriv ℝ i f x‖ := h_le
    _ = 1 * ‖iteratedFDeriv ℝ i f x‖ := by rw [h_norm]
    _ = ‖iteratedFDeriv ℝ i f x‖ := one_mul _

lemma norm_im_iteratedFDeriv_le (i : ℕ) (f : (Fin n → ℝ) → ℂ)
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (x : Fin n → ℝ) :
    ‖iteratedFDeriv ℝ i (fun y => (f y).im) x‖ ≤ ‖iteratedFDeriv ℝ i f x‖ := by
  have h_comp : (fun y => (f y).im) = Complex.imCLM ∘ f := rfl
  rw [h_comp]
  have h_diff : ContDiffAt ℝ (↑(⊤ : ℕ∞)) f x := hf.contDiffAt
  have h_le : (i : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) :=
    WithTop.coe_le_coe.mpr le_top
  rw [ContinuousLinearMap.iteratedFDeriv_comp_left Complex.imCLM h_diff h_le]
  have h_le :=
    ContinuousLinearMap.norm_compContinuousMultilinearMap_le Complex.imCLM
      (iteratedFDeriv ℝ i f x)
  have h_norm : ‖Complex.imCLM‖ = 1 := Complex.imCLM_norm
  calc ‖Complex.imCLM.compContinuousMultilinearMap (iteratedFDeriv ℝ i f x)‖
    _ ≤ ‖Complex.imCLM‖ * ‖iteratedFDeriv ℝ i f x‖ := h_le
    _ = 1 * ‖iteratedFDeriv ℝ i f x‖ := by rw [h_norm]
    _ = ‖iteratedFDeriv ℝ i f x‖ := one_mul _

lemma chi_mul_rem_smooth (Ω_n : Opens (Fin n → ℝ)) (χ : 𝓓(Ω_n, ℝ)) (z h : Fin n → ℂ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun y => (χ.toFun y : ℂ) * expTaylorRem z h y) := by
  have h1 : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun y => (χ.toFun y : ℂ)) := by
    have hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) χ.toFun := χ.contDiff' (n := ⊤)
    exact (ContinuousLinearMap.contDiff Complex.ofRealCLM).comp hχ
  have h2 : ContDiff ℝ (↑(⊤ : ℕ∞)) (expTaylorRem z h) :=
    expTaylorRem_smooth z h
  exact h1.mul h2

noncomputable def deriv_k_term (z : Fin n → ℂ) (k : Fin n) (x : Fin n → ℝ) : ℂ :=
  (-Complex.I * (x k : ℂ)) * Complex.exp (-Complex.I * (∑ i, z i * (x i : ℂ)))

lemma deriv_k_term_smooth (z : Fin n → ℂ) (k : Fin n) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => deriv_k_term z k x) := by
  dsimp [deriv_k_term]
  apply ContDiff.mul
  · apply ContDiff.mul
    · exact contDiff_const
    · exact x_i_smooth k
  · exact exp_izx_smooth z

lemma deriv_k_term_re_smooth (z : Fin n → ℂ) (k : Fin n) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (deriv_k_term z k x).re) :=
  Complex.reCLM.contDiff.comp (deriv_k_term_smooth z k)

lemma deriv_k_term_im_smooth (z : Fin n → ℂ) (k : Fin n) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x => (deriv_k_term z k x).im) :=
  Complex.imCLM.contDiff.comp (deriv_k_term_smooth z k)

lemma fourier_laplace_deriv_eq
    (T : 𝓓'(Ω_n, ℂ)) (hT : HasCompactSupport Ω_n T)
    (V : Opens (Fin n → ℝ)) (hV : Distribution.support Ω_n T ⊆ (V : Set (Fin n → ℝ)))
    (χ : 𝓓(Ω_n, ℝ)) (hχ_one : ∀ x ∈ (V : Set (Fin n → ℝ)), χ x = 1)
    (z : Fin n → ℂ) (k : Fin n) :
    FourierLaplaceDeriv Ω_n T hT V hV χ hχ_one k z =
    applySmoothComplex Ω_n T hT (deriv_k_term z k)
      (deriv_k_term_re_smooth z k) (deriv_k_term_im_smooth z k) V hV χ hχ_one := by
  dsimp [FourierLaplaceDeriv]
  have h_re : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun (x : Fin n → ℝ) =>
      (-Complex.I * ((x k : ℂ) * Complex.exp (-Complex.I * (∑ i, z i * (x i : ℂ))))).re) :=
    Complex.reCLM.contDiff.comp (contDiff_const.mul (x_mul_exp_izx_smooth z k))
  have h_im : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun (x : Fin n → ℝ) =>
      (-Complex.I * ((x k : ℂ) * Complex.exp (-Complex.I * (∑ i, z i * (x i : ℂ))))).im) :=
    Complex.imCLM.contDiff.comp (contDiff_const.mul (x_mul_exp_izx_smooth z k))
  have h_const := applySmoothComplex_const_mul Ω_n T hT V hV χ hχ_one (-Complex.I)
    (fun (x : Fin n → ℝ) => (x k : ℂ) * Complex.exp (-Complex.I * (∑ i, z i * (x i : ℂ))))
    (x_mul_exp_izx_re_smooth z k) (x_mul_exp_izx_im_smooth z k)
    h_re h_im
  rw [← h_const]
  apply applySmoothComplex_congr Ω_n T hT _ _ h_re h_im
    (deriv_k_term_re_smooth z k) (deriv_k_term_im_smooth z k) (fun x => by
    dsimp [deriv_k_term]
    ring)

lemma fourier_laplace_deriv_term
    (T : 𝓓'(Ω_n, ℂ)) (hT : HasCompactSupport Ω_n T)
    (V : Opens (Fin n → ℝ)) (hV : Distribution.support Ω_n T ⊆ (V : Set (Fin n → ℝ)))
    (χ : 𝓓(Ω_n, ℝ)) (hχ_one : ∀ x ∈ (V : Set (Fin n → ℝ)), χ x = 1)
    (z : Fin n → ℂ) (k : Fin n) (c : ℂ) :
    c * FourierLaplaceDeriv Ω_n T hT V hV χ hχ_one k z =
    applySmoothComplex Ω_n T hT (fun x => c * deriv_k_term z k x)
      (Complex.reCLM.contDiff.comp (contDiff_const.mul (deriv_k_term_smooth z k)))
      (Complex.imCLM.contDiff.comp (contDiff_const.mul (deriv_k_term_smooth z k)))
      V hV χ hχ_one := by
  rw [fourier_laplace_deriv_eq]
  have h_const := applySmoothComplex_const_mul Ω_n T hT V hV χ hχ_one c
    (deriv_k_term z k) (deriv_k_term_re_smooth z k) (deriv_k_term_im_smooth z k)
    (Complex.reCLM.contDiff.comp (contDiff_const.mul (deriv_k_term_smooth z k)))
    (Complex.imCLM.contDiff.comp (contDiff_const.mul (deriv_k_term_smooth z k)))
  rw [h_const]

lemma fourier_laplace_total_deriv_eq
    (T : 𝓓'(Ω_n, ℂ)) (hT : HasCompactSupport Ω_n T)
    (V : Opens (Fin n → ℝ)) (hV : Distribution.support Ω_n T ⊆ (V : Set (Fin n → ℝ)))
    (χ : 𝓓(Ω_n, ℝ)) (hχ_one : ∀ x ∈ (V : Set (Fin n → ℝ)), χ x = 1)
    (z h : Fin n → ℂ) :
    FourierLaplaceTotalDeriv Ω_n T hT V hV χ hχ_one z h =
    applySmoothComplex Ω_n T hT
      (fun x => ∑ k, h k * deriv_k_term z k x)
      (Complex.reCLM.contDiff.comp
        (ContDiff.sum (fun k _ => contDiff_const.mul (deriv_k_term_smooth z k))))
      (Complex.imCLM.contDiff.comp
        (ContDiff.sum (fun k _ => contDiff_const.mul (deriv_k_term_smooth z k))))
      V hV χ hχ_one := by
  rw [FourierLaplaceTotalDeriv_apply]
  have h_term : (fun k => h k * FourierLaplaceDeriv Ω_n T hT V hV χ hχ_one k z) =
      fun k => applySmoothComplex Ω_n T hT (fun x => h k * deriv_k_term z k x)
        (Complex.reCLM.contDiff.comp (contDiff_const.mul (deriv_k_term_smooth z k)))
        (Complex.imCLM.contDiff.comp (contDiff_const.mul (deriv_k_term_smooth z k)))
        V hV χ hχ_one := by
    ext k
    exact fourier_laplace_deriv_term Ω_n T hT V hV χ hχ_one z k (h k)
  rw [h_term]
  exact (applySmoothComplex_sum Ω_n Finset.univ T hT
    (fun k x => h k * deriv_k_term z k x)
    (fun k => Complex.reCLM.contDiff.comp (contDiff_const.mul (deriv_k_term_smooth z k)))
    (fun k => Complex.imCLM.contDiff.comp (contDiff_const.mul (deriv_k_term_smooth z k)))
    _ _ V hV χ hχ_one).symm

lemma fourier_laplace_diff_rem
    (T : 𝓓'(Ω_n, ℂ)) (hT : HasCompactSupport Ω_n T)
    (V : Opens (Fin n → ℝ)) (hV : Distribution.support Ω_n T ⊆ (V : Set (Fin n → ℝ)))
    (χ : 𝓓(Ω_n, ℝ)) (hχ_one : ∀ x ∈ (V : Set (Fin n → ℝ)), χ x = 1)
    (z h : Fin n → ℂ) :
    FourierLaplaceTransform Ω_n T hT V hV χ hχ_one (z + h) -
    FourierLaplaceTransform Ω_n T hT V hV χ hχ_one z -
    FourierLaplaceTotalDeriv Ω_n T hT V hV χ hχ_one z h =
    applySmoothComplex Ω_n T hT (expTaylorRem z h)
      (expTaylorRem_re_smooth z h) (expTaylorRem_im_smooth z h) V hV χ hχ_one := by
  dsimp [FourierLaplaceTransform]
  rw [fourier_laplace_total_deriv_eq]
  rw [← applySmoothComplex_sub_sub]
  apply applySmoothComplex_congr Ω_n T hT _ _ _ _ _ _ (fun x => by
    rfl)

lemma bound_mul_le (C : ℝ≥0) (c : ℝ) (hc : 0 ≤ c) (h : Fin n → ℂ) (B : ℝ)
    (hB : B ≤ (c / (2 * (C : ℝ) + 1)) * ‖h‖) :
    (2 * (C : ℝ)) * B ≤ c * ‖h‖ := by
  have h_pos : 0 < 2 * (C : ℝ) + 1 := by positivity
  have h_nonneg : 0 ≤ 2 * (C : ℝ) := by positivity
  have h_norm : 0 ≤ ‖h‖ := norm_nonneg h
  have h_frac : (2 * (C : ℝ)) * (c / (2 * (C : ℝ) + 1)) ≤ c := by
    rw [mul_div_assoc']
    rw [div_le_iff₀ h_pos]
    nlinarith
  calc (2 * (C : ℝ)) * B
    _ ≤ (2 * (C : ℝ)) * ((c / (2 * (C : ℝ) + 1)) * ‖h‖) :=
      mul_le_mul_of_nonneg_left hB h_nonneg
    _ = ((2 * (C : ℝ)) * (c / (2 * (C : ℝ) + 1))) * ‖h‖ := by ring
    _ ≤ c * ‖h‖ :=
      mul_le_mul_of_nonneg_right h_frac h_norm

lemma expTaylorRem_bound_exists_of_single
    (Ω_n : Opens (Fin n → ℝ))
    (χ : 𝓓(Ω_n, ℝ)) (z : Fin n → ℂ)
    (h_single : ∀ (i : ℕ) (c : ℝ), 0 < c → ∀ᶠ (h : Fin n → ℂ) in nhds 0,
      ∀ x ∈ (⟨tsupport χ, χ.hasCompactSupport'⟩ : Compacts (Fin n → ℝ)),
        ‖iteratedFDeriv ℝ i (fun y => (χ.toFun y : ℂ) * expTaylorRem z h y) x‖ ≤ c * ‖h‖)
    (s : Finset ℕ) :
    let K : Compacts (Fin n → ℝ) := ⟨tsupport χ, χ.hasCompactSupport'⟩
    ∀ c > 0, ∀ᶠ (h : Fin n → ℂ) in nhds 0,
      (∀ i ∈ s, ∀ x ∈ (K : Set (Fin n → ℝ)),
        ‖iteratedFDeriv ℝ i (fun y => χ.toFun y * (expTaylorRem z h y).re) x‖ ≤ c * ‖h‖) ∧
      (∀ i ∈ s, ∀ x ∈ (K : Set (Fin n → ℝ)),
        ‖iteratedFDeriv ℝ i (fun y => χ.toFun y * (expTaylorRem z h y).im) x‖ ≤ c * ‖h‖) := by
  intro K c hc
  rw [Filter.eventually_and]
  constructor
  · rw [Filter.eventually_all_finset]
    intro i _hi
    have h_ev := h_single i c hc
    filter_upwards [h_ev] with h hh x hx
    have h_re := norm_re_iteratedFDeriv_le i
      (fun y => (χ.toFun y : ℂ) * expTaylorRem z h y)
      (chi_mul_rem_smooth Ω_n χ z h) x
    have h_eval : (fun y => ((χ.toFun y : ℂ) * expTaylorRem z h y).re) =
        fun y => χ.toFun y * (expTaylorRem z h y).re := by
      ext y
      simp [Complex.mul_re]
    rw [h_eval] at h_re
    exact h_re.trans (hh x hx)
  · rw [Filter.eventually_all_finset]
    intro i _hi
    have h_ev := h_single i c hc
    filter_upwards [h_ev] with h hh x hx
    have h_im := norm_im_iteratedFDeriv_le i
      (fun y => (χ.toFun y : ℂ) * expTaylorRem z h y)
      (chi_mul_rem_smooth Ω_n χ z h) x
    have h_eval : (fun y => ((χ.toFun y : ℂ) * expTaylorRem z h y).im) =
        fun y => χ.toFun y * (expTaylorRem z h y).im := by
      ext y
      simp [Complex.mul_im]
    rw [h_eval] at h_im
    exact h_im.trans (hh x hx)

lemma norm_expTaylorRem_le (z h : Fin n → ℂ) (x : Fin n → ℝ) :
    ‖expTaylorRem z h x‖ ≤
      ‖Complex.exp (-Complex.I * (∑ i, z i * (x i : ℂ)))‖ *
        (‖-Complex.I * (∑ i, h i * (x i : ℂ))‖ ^ 2 *
          Real.exp ‖-Complex.I * (∑ i, h i * (x i : ℂ))‖) := by
  rw [expTaylorRem_factor]
  rw [norm_mul]
  gcongr
  exact exp_two_rem _

lemma norm_sum_h_x_le (h : Fin n → ℂ) (x : Fin n → ℝ) :
    ‖-Complex.I * (∑ i, h i * (x i : ℂ))‖ ≤ ∑ i, ‖h i‖ * |x i| := by
  rw [norm_mul, norm_neg, Complex.norm_I, one_mul]
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro i _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]

lemma norm_sum_h_x_le_pi (h : Fin n → ℂ) (x : Fin n → ℝ) :
    (∑ i, ‖h i‖ * |x i|) ≤ (n : ℝ) * ‖h‖ * ‖x‖ := by
  have h1 : ∀ i, ‖h i‖ ≤ ‖h‖ := fun i => norm_le_pi_norm h i
  have h2 : ∀ i, |x i| ≤ ‖x‖ := fun i => norm_le_pi_norm x i
  have h3 : ∀ i, ‖h i‖ * |x i| ≤ ‖h‖ * ‖x‖ := by
    intro i
    exact mul_le_mul (h1 i) (h2 i) (abs_nonneg _) (norm_nonneg _)
  calc ∑ i, ‖h i‖ * |x i|
    _ ≤ ∑ i : Fin n, ‖h‖ * ‖x‖ := Finset.sum_le_sum (fun i _ => h3 i)
    _ = (n : ℝ) * (‖h‖ * ‖x‖) := by simp
    _ = (n : ℝ) * ‖h‖ * ‖x‖ := by ring

lemma norm_exp_izx_le (z : Fin n → ℂ) (x : Fin n → ℝ) :
    ‖Complex.exp (-Complex.I * (∑ i, z i * (x i : ℂ)))‖ ≤
      Real.exp ((n : ℝ) * ‖z‖ * ‖x‖) := by
  rw [Complex.norm_exp]
  have h_re : (-Complex.I * (∑ i, z i * (x i : ℂ))).re = ∑ i, (z i).im * x i := by
    simp only [neg_mul, Complex.neg_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      zero_mul, one_mul]
    have h_im : (∑ i, z i * (x i : ℂ)).im = ∑ i, ((z i * (x i : ℂ)).im) :=
      map_sum Complex.imCLM _ _
    rw [zero_sub, neg_neg, h_im]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add]
  rw [h_re]
  apply Real.exp_le_exp_of_le
  calc ∑ i, (z i).im * x i
    _ ≤ ∑ i, |(z i).im * x i| := Finset.sum_le_sum (fun i _ => le_abs_self _)
    _ = ∑ i, |(z i).im| * |x i| := by simp_rw [abs_mul]
    _ ≤ ∑ i, ‖z i‖ * |x i| := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right (Complex.abs_im_le_norm (z i)) (abs_nonneg _)
    _ ≤ (n : ℝ) * ‖z‖ * ‖x‖ := by
      have h1 : ∀ i, ‖z i‖ ≤ ‖z‖ := fun i => norm_le_pi_norm z i
      have h2 : ∀ i, |x i| ≤ ‖x‖ := fun i => norm_le_pi_norm x i
      have h3 : ∀ i, ‖z i‖ * |x i| ≤ ‖z‖ * ‖x‖ := by
        intro i
        exact mul_le_mul (h1 i) (h2 i) (abs_nonneg _) (norm_nonneg _)
      calc ∑ i, ‖z i‖ * |x i|
        _ ≤ ∑ i : Fin n, ‖z‖ * ‖x‖ := Finset.sum_le_sum (fun i _ => h3 i)
        _ = (n : ℝ) * (‖z‖ * ‖x‖) := by simp
        _ = (n : ℝ) * ‖z‖ * ‖x‖ := by ring

lemma exists_norm_le_of_compact (K : Compacts (Fin n → ℝ)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ K, ‖x‖ ≤ M := by
  rcases K.isCompact'.isBounded.subset_ball 0 with ⟨M, hM⟩
  refine ⟨max 0 M, le_max_left 0 M, ?_⟩
  intro x hx
  have h := hM hx
  rw [Metric.mem_ball, dist_zero_right] at h
  exact h.le.trans (le_max_right 0 M)

lemma exists_norm_iteratedFDeriv_bound (Ω_n : Opens (Fin n → ℝ)) (χ : 𝓓(Ω_n, ℝ)) (j : ℕ) :
    let K : Compacts (Fin n → ℝ) := ⟨tsupport χ, χ.hasCompactSupport'⟩
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ K, ‖iteratedFDeriv ℝ j (fun y => (χ.toFun y : ℂ)) x‖ ≤ M := by
  intro K
  have hχ : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun y => (χ.toFun y : ℂ)) := by
    have h1 : ContDiff ℝ (↑(⊤ : ℕ∞)) χ.toFun := χ.contDiff' (n := ⊤)
    exact (ContinuousLinearMap.contDiff Complex.ofRealCLM).comp h1
  have hj : (j : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.mpr le_top
  have h_cont : Continuous (fun x => ‖iteratedFDeriv ℝ j (fun y => (χ.toFun y : ℂ)) x‖) :=
    (hχ.continuous_iteratedFDeriv hj).norm
  rcases K.isCompact'.bddAbove_image h_cont.continuousOn with ⟨M, hM⟩
  refine ⟨max 0 M, le_max_left 0 M, ?_⟩
  intro x hx
  have h := hM (mem_image_of_mem _ hx)
  exact h.trans (le_max_right 0 M)

lemma expTaylorRem_zero_bound_exists
    (Ω_n : Opens (Fin n → ℝ))
    (χ : 𝓓(Ω_n, ℝ)) (z : Fin n → ℂ) :
    let K : Compacts (Fin n → ℝ) := ⟨tsupport χ, χ.hasCompactSupport'⟩
    ∀ c > 0, ∀ᶠ (h : Fin n → ℂ) in nhds 0,
      ∀ x ∈ (K : Set (Fin n → ℝ)),
        ‖(χ.toFun x : ℂ) * expTaylorRem z h x‖ ≤ c * ‖h‖ := by
  intro K c hc
  rcases exists_norm_le_of_compact K with ⟨MK, hMK, hxMK⟩
  rcases exists_norm_iteratedFDeriv_bound Ω_n χ 0 with ⟨Mχ, hMχ, hxMχ⟩
  simp only [norm_iteratedFDeriv_zero] at hxMχ
  let Ez := Real.exp ((n : ℝ) * ‖z‖ * MK)
  have hEz_pos : 0 < Ez := Real.exp_pos _
  let Eh1 := Real.exp ((n : ℝ) * 1 * MK)
  let C := Mχ * Ez * ((n : ℝ) * MK)^2 * Eh1
  have hC_nonneg : 0 ≤ C := by positivity
  let δ := min (1 : ℝ) (c / (C + 1))
  have hδ_pos : 0 < δ := lt_min zero_lt_one (div_pos hc (by linarith))
  rw [Metric.eventually_nhds_iff]
  refine ⟨δ, hδ_pos, ?_⟩
  intro h hh x hx
  rw [dist_zero_right] at hh
  have hh1 : ‖h‖ ≤ 1 := (le_of_lt hh).trans (min_le_left 1 _)
  have hhC : ‖h‖ ≤ c / (C + 1) := (le_of_lt hh).trans (min_le_right 1 _)
  have hx_le : ‖x‖ ≤ MK := hxMK x hx
  have h_exp_z : ‖Complex.exp (-Complex.I * (∑ i, z i * (x i : ℂ)))‖ ≤ Ez := by
    have h1 := norm_exp_izx_le z x
    have h2 : (n : ℝ) * ‖z‖ * ‖x‖ ≤ (n : ℝ) * ‖z‖ * MK := by
      gcongr
    exact h1.trans (Real.exp_le_exp_of_le h2)
  have hu_le : ‖-Complex.I * (∑ i, h i * (x i : ℂ))‖ ≤ (n : ℝ) * ‖h‖ * MK := by
    have h1 := norm_sum_h_x_le h x
    have h2 := norm_sum_h_x_le_pi h x
    have h3 : (n : ℝ) * ‖h‖ * ‖x‖ ≤ (n : ℝ) * ‖h‖ * MK := by
      gcongr
    exact (h1.trans h2).trans h3
  have hu_le1 : ‖-Complex.I * (∑ i, h i * (x i : ℂ))‖ ≤ (n : ℝ) * 1 * MK := by
    calc ‖-Complex.I * (∑ i, h i * (x i : ℂ))‖
      _ ≤ (n : ℝ) * ‖h‖ * MK := hu_le
      _ ≤ (n : ℝ) * 1 * MK := by gcongr
  have h_exp_u : Real.exp ‖-Complex.I * (∑ i, h i * (x i : ℂ))‖ ≤ Eh1 :=
    Real.exp_le_exp_of_le hu_le1
  have h_rem := norm_expTaylorRem_le z h x
  have h_u2 : ‖-Complex.I * (∑ i, h i * (x i : ℂ))‖ ^ 2 ≤ ((n : ℝ) * MK)^2 * ‖h‖^2 := by
    have h_nonneg : 0 ≤ ‖-Complex.I * (∑ i, h i * (x i : ℂ))‖ := norm_nonneg _
    have h_ring : ((n : ℝ) * ‖h‖ * MK)^2 = ((n : ℝ) * MK)^2 * ‖h‖^2 := by ring
    rw [← h_ring]
    nlinarith
  have h_rem_bound : ‖expTaylorRem z h x‖ ≤ Ez * (((n : ℝ) * MK)^2 * Eh1) * ‖h‖^2 := by
    calc ‖expTaylorRem z h x‖
      _ ≤ ‖Complex.exp (-Complex.I * (∑ i, z i * (x i : ℂ)))‖ *
            (‖-Complex.I * (∑ i, h i * (x i : ℂ))‖ ^ 2 *
              Real.exp ‖-Complex.I * (∑ i, h i * (x i : ℂ))‖) := h_rem
      _ ≤ Ez * (((n : ℝ) * MK)^2 * ‖h‖^2 * Eh1) := by
        apply mul_le_mul h_exp_z _ (by positivity) (by positivity)
        apply mul_le_mul h_u2 h_exp_u (by positivity) (by positivity)
      _ = Ez * (((n : ℝ) * MK)^2 * Eh1) * ‖h‖^2 := by ring
  calc ‖(χ.toFun x : ℂ) * expTaylorRem z h x‖
    _ = ‖(χ.toFun x : ℂ)‖ * ‖expTaylorRem z h x‖ := norm_mul _ _
    _ ≤ Mχ * (Ez * (((n : ℝ) * MK)^2 * Eh1) * ‖h‖^2) :=
      mul_le_mul (hxMχ x hx) h_rem_bound (norm_nonneg _) hMχ
    _ = C * ‖h‖^2 := by
      dsimp [C]
      ring
    _ = (C * ‖h‖) * ‖h‖ := by ring
    _ ≤ (C * (c / (C + 1))) * ‖h‖ := by
      gcongr
    _ ≤ c * ‖h‖ := by
      have h_frac : C * (c / (C + 1)) ≤ c := by
        rw [mul_div_assoc']
        have h_pos : 0 < C + 1 := by positivity
        rw [div_le_iff₀ h_pos]
        nlinarith
      exact mul_le_mul_of_nonneg_right h_frac (norm_nonneg _)

lemma expTaylorRem_single_zero_bound_exists
    (Ω_n : Opens (Fin n → ℝ))
    (χ : 𝓓(Ω_n, ℝ)) (z : Fin n → ℂ) :
    let K : Compacts (Fin n → ℝ) := ⟨tsupport χ, χ.hasCompactSupport'⟩
    ∀ c > 0, ∀ᶠ (h : Fin n → ℂ) in nhds 0,
      ∀ x ∈ (K : Set (Fin n → ℝ)),
        ‖iteratedFDeriv ℝ 0 (fun y => (χ.toFun y : ℂ) * expTaylorRem z h y) x‖ ≤ c * ‖h‖ := by
  intro K c hc
  have h := expTaylorRem_zero_bound_exists Ω_n χ z c hc
  filter_upwards [h] with w hw x hx
  rw [norm_iteratedFDeriv_zero]
  exact hw x hx

noncomputable def g_rem (w : ℂ) : ℂ := Complex.exp w - 1 - w

lemma g_rem_smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) g_rem := by
  change ContDiff ℝ (↑(⊤ : ℕ∞)) (fun w => Complex.exp w - 1 - w)
  exact ContDiff.sub (ContDiff.sub contDiff_id.cexp contDiff_const) contDiff_id

noncomputable def L_h (h : Fin n → ℂ) : (Fin n → ℝ) →L[ℝ] ℂ :=
  -Complex.I • (∑ i, (h i) • (Complex.ofRealCLM.comp (ContinuousLinearMap.proj i)))

lemma L_h_apply (h : Fin n → ℂ) (x : Fin n → ℝ) :
    L_h h x = -Complex.I * (∑ i, h i * (x i : ℂ)) := by
  dsimp [L_h]
  simp only [smul_apply, _root_.sum_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    Complex.ofRealCLM_apply, smul_eq_mul]

lemma opNorm_L_h_le (h : Fin n → ℂ) :
    ‖L_h h‖ ≤ (n : ℝ) * ‖h‖ := by
  have h_nonneg : 0 ≤ (n : ℝ) * ‖h‖ := by positivity
  refine opNorm_le_bound _ h_nonneg ?_
  intro x
  rw [L_h_apply]
  have h1 := norm_sum_h_x_le h x
  have h2 := norm_sum_h_x_le_pi h x
  exact h1.trans h2

lemma norm_L_h_apply_le (h : Fin n → ℂ) (x : Fin n → ℝ) :
    ‖L_h h x‖ ≤ (n : ℝ) * ‖h‖ * ‖x‖ := by
  rw [L_h_apply]
  have h1 := norm_sum_h_x_le h x
  have h2 := norm_sum_h_x_le_pi h x
  exact h1.trans h2

lemma norm_iteratedFDeriv_comp_L_h_le (h : Fin n → ℂ) (k : ℕ) (x : Fin n → ℝ) :
    ‖iteratedFDeriv ℝ k (g_rem ∘ L_h h) x‖ ≤
      ‖iteratedFDeriv ℝ k g_rem (L_h h x)‖ * ‖L_h h‖ ^ k := by
  have hk : (k : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.mpr le_top
  rw [ContinuousLinearMap.iteratedFDeriv_comp_right (L_h h) g_rem_smooth x hk]
  have h_le := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv ℝ k g_rem (L_h h x)) (fun _ => L_h h)
  refine h_le.trans ?_
  have h_prod : (∏ _i : Fin k, ‖L_h h‖) = ‖L_h h‖ ^ k := by
    simp
  rw [h_prod]

lemma hasFDerivAt_g_rem_zero : HasFDerivAt g_rem (0 : ℂ →L[ℝ] ℂ) 0 := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  rw [Metric.eventually_nhds_iff]
  let δ := min (1 : ℝ) (c / (Real.exp 1))
  have hδ_pos : 0 < δ := lt_min zero_lt_one (div_pos hc (by positivity))
  refine ⟨δ, hδ_pos, ?_⟩
  intro w hw
  rw [dist_zero_right] at hw
  have hw1 : ‖w‖ ≤ 1 := (le_of_lt hw).trans (min_le_left 1 _)
  have hwc : ‖w‖ ≤ c / (Real.exp 1) := (le_of_lt hw).trans (min_le_right 1 _)
  dsimp [g_rem]
  simp only [zero_add, Complex.exp_zero, sub_self, sub_zero, zero_apply]
  have h_rem := exp_two_rem w
  have h_exp : Real.exp ‖w‖ ≤ Real.exp 1 := Real.exp_le_exp_of_le hw1
  calc ‖Complex.exp w - 1 - w‖
    _ ≤ ‖w‖ ^ 2 * Real.exp ‖w‖ := h_rem
    _ ≤ (‖w‖ * (c / Real.exp 1)) * Real.exp 1 := by
      have h_w2 : ‖w‖ ^ 2 ≤ ‖w‖ * (c / Real.exp 1) := by
        rw [pow_two]
        exact mul_le_mul_of_nonneg_left hwc (norm_nonneg _)
      exact mul_le_mul h_w2 h_exp (Real.exp_pos _).le (by positivity)
    _ = ‖w‖ * ((c / Real.exp 1) * Real.exp 1) := by ring
    _ = ‖w‖ * c := by
      have h_ne : Real.exp 1 ≠ 0 := Real.exp_ne_zero 1
      rw [div_mul_cancel₀ _ h_ne]
    _ = c * ‖w‖ := mul_comm _ _

lemma fderiv_g_rem_zero : fderiv ℝ g_rem 0 = 0 :=
  hasFDerivAt_g_rem_zero.fderiv

lemma norm_iteratedFDeriv_one_g_rem_le (R : ℝ) (hR : 0 ≤ R) (C2 : ℝ)
    (hC2 : ∀ w : ℂ, ‖w‖ ≤ R → ‖iteratedFDeriv ℝ 2 g_rem w‖ ≤ C2) :
    ∀ w : ℂ, ‖w‖ ≤ R → ‖iteratedFDeriv ℝ 1 g_rem w‖ ≤ C2 * ‖w‖ := by
  intro w hw
  have hle : (1 : WithTop ℕ∞) + 1 ≤ ↑(⊤ : ℕ∞) := WithTop.coe_le_coe.mpr le_top
  have h_contdiff : ContDiff ℝ 1 (fderiv ℝ g_rem) :=
    ContDiff.fderiv_right (m := 1) g_rem_smooth hle
  have h_diff : ∀ y ∈ Metric.closedBall (0 : ℂ) R,
      DifferentiableAt ℝ (fderiv ℝ g_rem) y := by
    intro y _
    exact (h_contdiff.differentiable one_ne_zero).differentiableAt
  have h_bound : ∀ y ∈ Metric.closedBall (0 : ℂ) R,
      ‖fderiv ℝ (fderiv ℝ g_rem) y‖ ≤ C2 := by
    intro y hy
    rw [Metric.mem_closedBall, dist_zero_right] at hy
    have h1 : ‖fderiv ℝ (fderiv ℝ g_rem) y‖ = ‖iteratedFDeriv ℝ 1 (fderiv ℝ g_rem) y‖ := by
      rw [norm_iteratedFDeriv_one]
    have h2 : ‖iteratedFDeriv ℝ 1 (fderiv ℝ g_rem) y‖ = ‖iteratedFDeriv ℝ 2 g_rem y‖ := by
      exact norm_iteratedFDeriv_fderiv (n := 1)
    rw [h1, h2]
    exact hC2 y hy
  have h_conv : Convex ℝ (Metric.closedBall (0 : ℂ) R) := convex_closedBall 0 R
  have hw_mem : w ∈ Metric.closedBall (0 : ℂ) R := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hw
  have h0_mem : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) R := by
    rw [Metric.mem_closedBall, dist_zero_right, norm_zero]
    exact hR
  have h_mvt := Convex.norm_image_sub_le_of_norm_fderiv_le h_diff h_bound h_conv h0_mem hw_mem
  rw [fderiv_g_rem_zero, sub_zero, sub_zero] at h_mvt
  rw [norm_iteratedFDeriv_one]
  exact h_mvt

lemma exists_norm_iteratedFDeriv_g_rem_bound (k : ℕ) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, ‖w‖ ≤ R → ‖iteratedFDeriv ℝ k g_rem w‖ ≤ C := by
  by_cases hR : 0 ≤ R
  · have hk : (k : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.mpr le_top
    have h_cont : Continuous (fun w => ‖iteratedFDeriv ℝ k g_rem w‖) :=
      (g_rem_smooth.continuous_iteratedFDeriv hk).norm
    have h_comp : IsCompact (Metric.closedBall (0 : ℂ) R) := isCompact_closedBall 0 R
    rcases h_comp.bddAbove_image h_cont.continuousOn with ⟨M, hM⟩
    refine ⟨max 0 M, le_max_left 0 M, ?_⟩
    intro w hw
    have hw' : w ∈ Metric.closedBall (0 : ℂ) R := by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hw
    have hw_mem : (fun w => ‖iteratedFDeriv ℝ k g_rem w‖) w ∈
        (fun w => ‖iteratedFDeriv ℝ k g_rem w‖) '' Metric.closedBall (0 : ℂ) R :=
      mem_image_of_mem _ hw'
    exact (hM hw_mem).trans (le_max_right 0 M)
  · refine ⟨0, le_rfl, ?_⟩
    intro w hw
    have : 0 ≤ ‖w‖ := norm_nonneg _
    linarith

lemma pow_mul_norm_sq_le (h : Fin n → ℂ) (hh : ‖h‖ ≤ 1) (k : ℕ) (hk : 2 ≤ k) :
    ((n : ℝ) * ‖h‖) ^ k ≤ (n : ℝ) ^ k * ‖h‖ ^ 2 := by
  rw [mul_pow]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact pow_le_pow_of_le_one (norm_nonneg _) hh hk

lemma exists_g_rem_comp_L_h_bound_sq (MK : ℝ) (hMK : 0 ≤ MK) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (h : Fin n → ℂ) (_hh : ‖h‖ ≤ 1) (x : Fin n → ℝ) (_hx : ‖x‖ ≤ MK),
      ‖iteratedFDeriv ℝ k (g_rem ∘ L_h h) x‖ ≤ C * ‖h‖ ^ 2 := by
  let R := (n : ℝ) * MK
  have hR : 0 ≤ R := by positivity
  rcases k with _ | k
  · refine ⟨((n : ℝ) * MK) ^ 2 * Real.exp R, by positivity, ?_⟩
    intro h hh x hx
    rw [norm_iteratedFDeriv_zero]
    dsimp [Function.comp]
    have h_rem := exp_two_rem (L_h h x)
    have hx_le : ‖L_h h x‖ ≤ (n : ℝ) * ‖h‖ * ‖x‖ := norm_L_h_apply_le h x
    have hx_le' : ‖L_h h x‖ ≤ ((n : ℝ) * MK) * ‖h‖ := by
      calc ‖L_h h x‖
        _ ≤ (n : ℝ) * ‖h‖ * ‖x‖ := hx_le
        _ ≤ (n : ℝ) * ‖h‖ * MK :=
          mul_le_mul_of_nonneg_left hx (by positivity)
        _ = ((n : ℝ) * MK) * ‖h‖ := by ring
    have h_w_le_R : ‖L_h h x‖ ≤ R := by
      calc ‖L_h h x‖
        _ ≤ ((n : ℝ) * MK) * ‖h‖ := hx_le'
        _ ≤ ((n : ℝ) * MK) * 1 :=
          mul_le_mul_of_nonneg_left hh (by positivity)
        _ = R := by ring
    have h_exp : Real.exp ‖L_h h x‖ ≤ Real.exp R := Real.exp_le_exp_of_le h_w_le_R
    have h_sq : ‖L_h h x‖ ^ 2 ≤ (((n : ℝ) * MK) * ‖h‖) ^ 2 := by
      have : 0 ≤ ‖L_h h x‖ := norm_nonneg _
      exact sq_le_sq' (by linarith) hx_le'
    calc ‖Complex.exp (L_h h x) - 1 - L_h h x‖
      _ ≤ ‖L_h h x‖ ^ 2 * Real.exp ‖L_h h x‖ := h_rem
      _ ≤ (((n : ℝ) * MK) * ‖h‖) ^ 2 * Real.exp R :=
        mul_le_mul h_sq h_exp (Real.exp_pos _).le (by positivity)
      _ = (((n : ℝ) * MK) ^ 2 * Real.exp R) * ‖h‖ ^ 2 := by ring
  · rcases k with _ | k
    · rcases exists_norm_iteratedFDeriv_g_rem_bound 2 R with ⟨C2, hC2_nonneg, hC2⟩
      refine ⟨C2 * (n : ℝ) ^ 2 * MK, by positivity, ?_⟩
      intro h hh x hx
      have h_comp_le := norm_iteratedFDeriv_comp_L_h_le h 1 x
      rw [pow_one] at h_comp_le
      have hx_le : ‖L_h h x‖ ≤ (n : ℝ) * ‖h‖ * ‖x‖ := norm_L_h_apply_le h x
      have hx_le' : ‖L_h h x‖ ≤ ((n : ℝ) * MK) * ‖h‖ := by
        calc ‖L_h h x‖
          _ ≤ (n : ℝ) * ‖h‖ * ‖x‖ := hx_le
          _ ≤ (n : ℝ) * ‖h‖ * MK :=
            mul_le_mul_of_nonneg_left hx (by positivity)
          _ = ((n : ℝ) * MK) * ‖h‖ := by ring
      have h_w_le_R : ‖L_h h x‖ ≤ R := by
        calc ‖L_h h x‖
          _ ≤ ((n : ℝ) * MK) * ‖h‖ := hx_le'
          _ ≤ ((n : ℝ) * MK) * 1 :=
            mul_le_mul_of_nonneg_left hh (by positivity)
          _ = R := by ring
      have h_g1 : ‖iteratedFDeriv ℝ 1 g_rem (L_h h x)‖ ≤ C2 * ‖L_h h x‖ :=
        norm_iteratedFDeriv_one_g_rem_le R hR C2 hC2 (L_h h x) h_w_le_R
      have h_op : ‖L_h h‖ ≤ (n : ℝ) * ‖h‖ := opNorm_L_h_le h
      calc ‖iteratedFDeriv ℝ 1 (g_rem ∘ L_h h) x‖
        _ ≤ ‖iteratedFDeriv ℝ 1 g_rem (L_h h x)‖ * ‖L_h h‖ := h_comp_le
        _ ≤ (C2 * ‖L_h h x‖) * ((n : ℝ) * ‖h‖) :=
          mul_le_mul h_g1 h_op (norm_nonneg _) (by positivity)
        _ ≤ (C2 * (((n : ℝ) * MK) * ‖h‖)) * ((n : ℝ) * ‖h‖) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left hx_le' hC2_nonneg
        _ = (C2 * (n : ℝ) ^ 2 * MK) * ‖h‖ ^ 2 := by ring
    · let m := k + 2
      have hm : 2 ≤ m := by omega
      rcases exists_norm_iteratedFDeriv_g_rem_bound m R with ⟨Cm, hCm_nonneg, hCm⟩
      refine ⟨Cm * (n : ℝ) ^ m, by positivity, ?_⟩
      intro h hh x hx
      have h_comp_le := norm_iteratedFDeriv_comp_L_h_le h m x
      have h_w_le_R : ‖L_h h x‖ ≤ R := by
        have hx_le := norm_L_h_apply_le h x
        calc ‖L_h h x‖
          _ ≤ (n : ℝ) * ‖h‖ * ‖x‖ := hx_le
          _ ≤ (n : ℝ) * 1 * MK := by
            refine mul_le_mul ?_ hx (norm_nonneg _) (by positivity)
            exact mul_le_mul_of_nonneg_left hh (by positivity)
          _ = R := by ring
      have h_gm : ‖iteratedFDeriv ℝ m g_rem (L_h h x)‖ ≤ Cm := hCm (L_h h x) h_w_le_R
      have h_op : ‖L_h h‖ ≤ (n : ℝ) * ‖h‖ := opNorm_L_h_le h
      have h_op_pow : ‖L_h h‖ ^ m ≤ ((n : ℝ) * ‖h‖) ^ m :=
        pow_le_pow_left₀ (norm_nonneg _) h_op m
      have h_pow_le : ((n : ℝ) * ‖h‖) ^ m ≤ (n : ℝ) ^ m * ‖h‖ ^ 2 :=
        pow_mul_norm_sq_le h hh m hm
      calc ‖iteratedFDeriv ℝ m (g_rem ∘ L_h h) x‖
        _ ≤ ‖iteratedFDeriv ℝ m g_rem (L_h h x)‖ * ‖L_h h‖ ^ m := h_comp_le
        _ ≤ Cm * ((n : ℝ) ^ m * ‖h‖ ^ 2) := by
          refine mul_le_mul h_gm (h_op_pow.trans h_pow_le) (by positivity) hCm_nonneg
        _ = (Cm * (n : ℝ) ^ m) * ‖h‖ ^ 2 := by ring

lemma expTaylorRem_eq_mul (z h : Fin n → ℂ) (x : Fin n → ℝ) :
    expTaylorRem z h x =
      Complex.exp (-Complex.I * (∑ i, z i * (x i : ℂ))) * (g_rem ∘ L_h h) x := by
  rw [expTaylorRem_factor]
  dsimp [g_rem, Function.comp]
  rw [L_h_apply]

noncomputable def chi_mul_exp (Ω_n : Opens (Fin n → ℝ)) (χ : 𝓓(Ω_n, ℝ)) (z : Fin n → ℂ) :
    (Fin n → ℝ) → ℂ :=
  fun y => (χ.toFun y : ℂ) * Complex.exp (-Complex.I * (∑ k, z k * (y k : ℂ)))

lemma chi_mul_exp_smooth (Ω_n : Opens (Fin n → ℝ)) (χ : 𝓓(Ω_n, ℝ)) (z : Fin n → ℂ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (chi_mul_exp Ω_n χ z) := by
  have h1 : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun y => (χ.toFun y : ℂ)) := by
    have hχ' : ContDiff ℝ (↑(⊤ : ℕ∞)) χ.toFun := χ.contDiff' (n := ⊤)
    exact (ContinuousLinearMap.contDiff Complex.ofRealCLM).comp hχ'
  have h2 := exp_izx_smooth z
  exact h1.mul h2

lemma exists_chi_mul_exp_bound (Ω_n : Opens (Fin n → ℝ)) (χ : 𝓓(Ω_n, ℝ)) (z : Fin n → ℂ) (j : ℕ) :
    let K : Compacts (Fin n → ℝ) := ⟨tsupport χ, χ.hasCompactSupport'⟩
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ K, ‖iteratedFDeriv ℝ j (chi_mul_exp Ω_n χ z) x‖ ≤ M := by
  intro K
  have hF := chi_mul_exp_smooth Ω_n χ z
  have hj : (j : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.mpr le_top
  have h_cont : Continuous (fun x => ‖iteratedFDeriv ℝ j (chi_mul_exp Ω_n χ z) x‖) :=
    (hF.continuous_iteratedFDeriv hj).norm
  rcases K.isCompact'.bddAbove_image h_cont.continuousOn with ⟨M, hM⟩
  refine ⟨max 0 M, le_max_left 0 M, ?_⟩
  intro x hx
  have h := hM (mem_image_of_mem _ hx)
  exact h.trans (le_max_right 0 M)

lemma expTaylorRem_fun_eq (Ω_n : Opens (Fin n → ℝ)) (χ : 𝓓(Ω_n, ℝ)) (z h : Fin n → ℂ) :
    (fun y => (χ.toFun y : ℂ) * expTaylorRem z h y) =
      (fun y => (chi_mul_exp Ω_n χ z y) * (g_rem ∘ L_h h) y) := by
  ext y
  dsimp [chi_mul_exp, Function.comp]
  rw [expTaylorRem_eq_mul]
  dsimp [Function.comp]
  ring

lemma expTaylorRem_single_bound_exists
    (Ω_n : Opens (Fin n → ℝ))
    (χ : 𝓓(Ω_n, ℝ)) (z : Fin n → ℂ) (i : ℕ) :
    let K : Compacts (Fin n → ℝ) := ⟨tsupport χ, χ.hasCompactSupport'⟩
    ∀ c > 0, ∀ᶠ (h : Fin n → ℂ) in nhds 0,
      ∀ x ∈ (K : Set (Fin n → ℝ)),
        ‖iteratedFDeriv ℝ i (fun y => (χ.toFun y : ℂ) * expTaylorRem z h y) x‖ ≤ c * ‖h‖ := by
  intro K c hc
  rcases exists_norm_le_of_compact K with ⟨MK, hMK, hxMK⟩
  have h_bound_F : ∀ j : ℕ, ∃ M : ℝ, 0 ≤ M ∧
      ∀ x ∈ (K : Set (Fin n → ℝ)), ‖iteratedFDeriv ℝ j (chi_mul_exp Ω_n χ z) x‖ ≤ M :=
    fun j => exists_chi_mul_exp_bound Ω_n χ z j
  have h_bound_G : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (h : Fin n → ℂ) (hh : ‖h‖ ≤ 1) (x : Fin n → ℝ) (hx : ‖x‖ ≤ MK),
        ‖iteratedFDeriv ℝ k (g_rem ∘ L_h h) x‖ ≤ C * ‖h‖ ^ 2 :=
    fun k => exists_g_rem_comp_L_h_bound_sq MK hMK k
  choose M_F hM_F_nonneg hM_F using h_bound_F
  choose C_G hC_G_nonneg hC_G using h_bound_G
  let C_total := ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * M_F j * C_G (i - j)
  have hC_total_nonneg : 0 ≤ C_total := by
    refine Finset.sum_nonneg ?_
    intro j _
    have h1 : 0 ≤ (i.choose j : ℝ) := by positivity
    have h2 := hM_F_nonneg j
    have h3 := hC_G_nonneg (i - j)
    positivity
  let δ := min (1 : ℝ) (c / (C_total + 1))
  have hδ_pos : 0 < δ := lt_min zero_lt_one (div_pos hc (by positivity))
  rw [Metric.eventually_nhds_iff]
  refine ⟨δ, hδ_pos, ?_⟩
  intro h hh
  rw [dist_zero_right] at hh
  have hh1 : ‖h‖ ≤ 1 := (le_of_lt hh).trans (min_le_left 1 _)
  have hhc : ‖h‖ ≤ c / (C_total + 1) := (le_of_lt hh).trans (min_le_right 1 _)
  intro x hx
  rw [expTaylorRem_fun_eq]
  have hF_smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) (chi_mul_exp Ω_n χ z) :=
    chi_mul_exp_smooth Ω_n χ z
  have hG_smooth : ContDiff ℝ (↑(⊤ : ℕ∞)) (g_rem ∘ L_h h) :=
    g_rem_smooth.comp (L_h h).contDiff
  have hi : (i : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.mpr le_top
  have h_leibniz := norm_iteratedFDeriv_mul_le hF_smooth hG_smooth x (n := i) hi
  have h_term : ∀ j ∈ Finset.range (i + 1),
      (i.choose j : ℝ) * ‖iteratedFDeriv ℝ j (chi_mul_exp Ω_n χ z) x‖ *
          ‖iteratedFDeriv ℝ (i - j) (g_rem ∘ L_h h) x‖ ≤
        ((i.choose j : ℝ) * M_F j * C_G (i - j)) * ‖h‖ ^ 2 := by
    intro j _
    have hF_le := hM_F j x hx
    have hG_le := hC_G (i - j) h hh1 x (hxMK x hx)
    have h_mul1 : ‖iteratedFDeriv ℝ j (chi_mul_exp Ω_n χ z) x‖ *
        ‖iteratedFDeriv ℝ (i - j) (g_rem ∘ L_h h) x‖ ≤
      (M_F j * C_G (i - j)) * ‖h‖ ^ 2 := by
      calc ‖iteratedFDeriv ℝ j (chi_mul_exp Ω_n χ z) x‖ *
          ‖iteratedFDeriv ℝ (i - j) (g_rem ∘ L_h h) x‖
        _ ≤ M_F j * (C_G (i - j) * ‖h‖ ^ 2) :=
          mul_le_mul hF_le hG_le (norm_nonneg _) (hM_F_nonneg j)
        _ = (M_F j * C_G (i - j)) * ‖h‖ ^ 2 := by ring
    calc (i.choose j : ℝ) * ‖iteratedFDeriv ℝ j (chi_mul_exp Ω_n χ z) x‖ *
          ‖iteratedFDeriv ℝ (i - j) (g_rem ∘ L_h h) x‖
      _ = (i.choose j : ℝ) * (‖iteratedFDeriv ℝ j (chi_mul_exp Ω_n χ z) x‖ *
          ‖iteratedFDeriv ℝ (i - j) (g_rem ∘ L_h h) x‖) := by ring
      _ ≤ (i.choose j : ℝ) * ((M_F j * C_G (i - j)) * ‖h‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h_mul1 (by positivity)
      _ = ((i.choose j : ℝ) * M_F j * C_G (i - j)) * ‖h‖ ^ 2 := by ring
  calc ‖iteratedFDeriv ℝ i (fun y => (chi_mul_exp Ω_n χ z y) * (g_rem ∘ L_h h) y) x‖
    _ ≤ ∑ j ∈ Finset.range (i + 1),
          (i.choose j : ℝ) * ‖iteratedFDeriv ℝ j (chi_mul_exp Ω_n χ z) x‖ *
            ‖iteratedFDeriv ℝ (i - j) (g_rem ∘ L_h h) x‖ := h_leibniz
    _ ≤ ∑ j ∈ Finset.range (i + 1),
          ((i.choose j : ℝ) * M_F j * C_G (i - j)) * ‖h‖ ^ 2 :=
        Finset.sum_le_sum h_term
    _ = C_total * ‖h‖ ^ 2 := by
      rw [← Finset.sum_mul]
    _ = (C_total * ‖h‖) * ‖h‖ := by ring
    _ ≤ c * ‖h‖ := by
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      have h_c : C_total * ‖h‖ ≤ C_total * (c / (C_total + 1)) :=
        mul_le_mul_of_nonneg_left hhc hC_total_nonneg
      refine h_c.trans ?_
      calc C_total * (c / (C_total + 1))
        _ = (C_total / (C_total + 1)) * c := by ring
        _ ≤ 1 * c := by
          refine mul_le_mul_of_nonneg_right ?_ hc.le
          have : C_total ≤ C_total + 1 := by linarith
          exact div_le_one_of_le₀ this (by positivity)
        _ = c := one_mul c

lemma expTaylorRem_bound_exists
    (Ω_n : Opens (Fin n → ℝ))
    (χ : 𝓓(Ω_n, ℝ)) (z : Fin n → ℂ) (s : Finset ℕ) :
    let K : Compacts (Fin n → ℝ) := ⟨tsupport χ, χ.hasCompactSupport'⟩
    ∀ c > 0, ∀ᶠ (h : Fin n → ℂ) in nhds 0,
      (∀ i ∈ s, ∀ x ∈ (K : Set (Fin n → ℝ)),
        ‖iteratedFDeriv ℝ i (fun y => χ.toFun y * (expTaylorRem z h y).re) x‖ ≤ c * ‖h‖) ∧
      (∀ i ∈ s, ∀ x ∈ (K : Set (Fin n → ℝ)),
        ‖iteratedFDeriv ℝ i (fun y => χ.toFun y * (expTaylorRem z h y).im) x‖ ≤ c * ‖h‖) := by
  apply expTaylorRem_bound_exists_of_single Ω_n χ z (expTaylorRem_single_bound_exists Ω_n χ z)

lemma fourier_laplace_hasFDerivAt
    (T : 𝓓'(Ω_n, ℂ)) (hT : HasCompactSupport Ω_n T)
    (V : Opens (Fin n → ℝ)) (hV : Distribution.support Ω_n T ⊆ (V : Set (Fin n → ℝ)))
    (χ : 𝓓(Ω_n, ℝ)) (hχ_one : ∀ x ∈ (V : Set (Fin n → ℝ)), χ x = 1) (z : Fin n → ℂ) :
    HasFDerivAt (FourierLaplaceTransform Ω_n T hT V hV χ hχ_one)
      (FourierLaplaceTotalDeriv Ω_n T hT V hV χ hχ_one z) z := by
  by_cases hn : n = 0
  · subst hn
    have h_deriv_zero : FourierLaplaceTotalDeriv Ω_n T hT V hV χ hχ_one z = 0 := by
      ext h
      rw [FourierLaplaceTotalDeriv_apply]
      simp only [Finset.univ_eq_empty, Finset.sum_empty]
      rfl
    rw [h_deriv_zero]
    have h_subsingleton : Subsingleton (Fin 0 → ℂ) := inferInstance
    have h_const : ∀ w : Fin 0 → ℂ, w = z := fun w => Subsingleton.elim w z
    have h_eq : (FourierLaplaceTransform Ω_n T hT V hV χ hχ_one) =
        fun _ => FourierLaplaceTransform Ω_n T hT V hV χ hχ_one z := by
      ext w
      rw [h_const w]
    rw [h_eq]
    exact hasFDerivAt_const (𝕜 := ℂ) _ z
  · by_cases h_supp : Distribution.support Ω_n T = ∅
    · exact fourier_laplace_empty_support Ω_n T hT h_supp V hV χ hχ_one z
    · have h_bound := applySmoothComplex_bound Ω_n T hT V hV χ hχ_one
      rcases h_bound with ⟨s, C, h_eval⟩
      rw [hasFDerivAt_iff_isLittleO_nhds_zero]
      rw [Asymptotics.isLittleO_iff]
      intro c hc
      have hc_pos : 0 < c / (2 * (C : ℝ) + 1) := by
        have h_denom : 0 < 2 * (C : ℝ) + 1 := by positivity
        exact div_pos hc h_denom
      have h_ev := expTaylorRem_bound_exists Ω_n χ z s (c / (2 * (C : ℝ) + 1)) hc_pos
      filter_upwards [h_ev] with h hh
      rw [fourier_laplace_diff_rem]
      have hB_nonneg : 0 ≤ (c / (2 * (C : ℝ) + 1)) * ‖h‖ :=
        mul_nonneg hc_pos.le (norm_nonneg h)
      have h_app := h_eval (expTaylorRem z h) (expTaylorRem_re_smooth z h)
        (expTaylorRem_im_smooth z h) ((c / (2 * (C : ℝ) + 1)) * ‖h‖) hB_nonneg hh.1 hh.2
      exact h_app.trans (bound_mul_le C c hc.le h _ le_rfl)

lemma FourierLaplaceTransform_is_entire
    (T : 𝓓'(Ω_n, ℂ)) (hT : HasCompactSupport Ω_n T)
    (V : Opens (Fin n → ℝ)) (hV : Distribution.support Ω_n T ⊆ (V : Set (Fin n → ℝ)))
    (χ : 𝓓(Ω_n, ℝ)) (hχ_one : ∀ x ∈ (V : Set (Fin n → ℝ)), χ x = 1) :
    Differentiable ℂ (FourierLaplaceTransform Ω_n T hT V hV χ hχ_one) := by
  intro z
  exact (fourier_laplace_hasFDerivAt Ω_n T hT V hV χ hχ_one z).differentiableAt

lemma FourierLaplaceTransform_is_holomorphic
    (T : 𝓓'(Ω_n, ℂ)) (hT : HasCompactSupport Ω_n T)
    (V : Opens (Fin n → ℝ)) (hV : Distribution.support Ω_n T ⊆ (V : Set (Fin n → ℝ)))
    (χ : 𝓓(Ω_n, ℝ)) (hχ_one : ∀ x ∈ (V : Set (Fin n → ℝ)), χ x = 1)
    (_h_supp : Distribution.support Ω_n T ⊆ DualCone V_plus) :
    DifferentiableOn ℂ (FourierLaplaceTransform Ω_n T hT V hV χ hχ_one) (TubeDomain V_plus) := by
  exact (FourierLaplaceTransform_is_entire Ω_n T hT V hV χ hχ_one).differentiableOn

def EqualOn (T₁ T₂ : 𝓓'(Ω_n, ℂ)) (U : Opens (Fin n → ℝ))
    (_hU : (U : Set (Fin n → ℝ)) ⊆ Ω_n) : Prop :=
  ∀ φ : 𝓓(Ω_n, ℝ), tsupport (fun x => φ x) ⊆ (U : Set (Fin n → ℝ)) → T₁ φ = T₂ φ

lemma local_eow_epstein_empty
    (V_plus V_minus : Set (Fin n → ℝ))
    (f_plus f_minus : (Fin n → ℂ) → ℂ)
    (U : Opens (Fin n → ℝ)) (hU_empty : (U : Set (Fin n → ℝ)) = ∅) :
    ∃ (W : Opens (Fin n → ℂ)) (F : (Fin n → ℂ) → ℂ),
      (∀ x ∈ U, (fun i => (x i : ℂ)) ∈ W) ∧
      DifferentiableOn ℂ F (W : Set (Fin n → ℂ)) ∧
      EqOn F f_plus ((W : Set (Fin n → ℂ)) ∩ TubeDomain V_plus) ∧
      EqOn F f_minus ((W : Set (Fin n → ℂ)) ∩ TubeDomain V_minus) := by
  refine ⟨⊥, 0, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hx_set : x ∈ (U : Set (Fin n → ℝ)) := hx
    rw [hU_empty] at hx_set
    exact False.elim hx_set
  · exact differentiableOn_empty
  · simp only [Opens.coe_bot, Set.empty_inter, eqOn_empty]
  · simp only [Opens.coe_bot, Set.empty_inter, eqOn_empty]

lemma local_eow_epstein_empty_tube
    (V_plus V_minus : Set (Fin n → ℝ))
    (h_opposite : V_minus = (fun y => -y) '' V_plus)
    (f_plus f_minus : (Fin n → ℂ) → ℂ)
    (U : Opens (Fin n → ℝ))
    (h_empty_tube : TubeDomain V_plus = ∅) :
    ∃ (W : Opens (Fin n → ℂ)) (F : (Fin n → ℂ) → ℂ),
      (∀ x ∈ U, (fun i => (x i : ℂ)) ∈ W) ∧
      DifferentiableOn ℂ F (W : Set (Fin n → ℂ)) ∧
      EqOn F f_plus ((W : Set (Fin n → ℂ)) ∩ TubeDomain V_plus) ∧
      EqOn F f_minus ((W : Set (Fin n → ℂ)) ∩ TubeDomain V_minus) := by
  refine ⟨⊤, 0, ?_, ?_, ?_, ?_⟩
  · intro x hx; trivial
  · exact differentiable_const 0 |>.differentiableOn
  · rw [h_empty_tube, Set.inter_empty]
    exact eqOn_empty _ _
  · have h_empty_minus : TubeDomain V_minus = ∅ := by
      rw [h_opposite]
      ext z
      simp only [mem_empty_iff_false, iff_false]
      intro hz
      have hz_im : (fun i => (z i).im) ∈ (fun y => -y) '' V_plus := hz
      rcases hz_im with ⟨y, hy, _⟩
      let z_test : Fin n → ℂ := fun j => (y j : ℂ) * Complex.I
      have hz_plus : (fun i => (z_test i).im) ∈ V_plus := by
        have : (fun i => (z_test i).im) = y := by
          ext i
          dsimp [z_test]
          simp only [Complex.mul_I_im, Complex.ofReal_re]
        rw [this]
        exact hy
      have : z_test ∈ TubeDomain V_plus := hz_plus
      rw [h_empty_tube] at this
      exact this
    rw [h_empty_minus, Set.inter_empty]
    exact eqOn_empty _ _

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
lemma tsupport_const_one_subsingleton [Subsingleton E] [TopologicalSpace E] :
    tsupport (fun _ : E => (1 : ℝ)) = Set.univ := by
  dsimp [tsupport, Function.support]
  simp

lemma exists_test_function_one (Ω : Opens (Fin 0 → ℝ))
    (hΩ : (Ω : Set (Fin 0 → ℝ)) = Set.univ) :
    ∃ φ : 𝓓(Ω, ℝ), (∀ x, φ x = 1) ∧ tsupport (fun x => φ x) ⊆ Set.univ := by
  have h_comp : _root_.HasCompactSupport (fun _ : Fin 0 → ℝ => (1 : ℝ)) := by
    dsimp [_root_.HasCompactSupport]
    rw [tsupport_const_one_subsingleton]
    exact isCompact_univ
  have h_tsupp : tsupport (fun _ : Fin 0 → ℝ => (1 : ℝ)) ⊆ (Ω : Set (Fin 0 → ℝ)) := by
    rw [hΩ, tsupport_const_one_subsingleton]
  refine ⟨⟨fun _ => 1, contDiff_const, h_comp, h_tsupp⟩, fun _ => rfl, by simp⟩

lemma boundaryIntegral_zero_dim (Ω_0 : Opens (Fin 0 → ℝ))
    (f : (Fin 0 → ℂ) → ℂ) (φ : 𝓓(Ω_0, ℝ)) (hφ : ∀ x, φ x = 1)
    (y : Fin 0 → ℝ) (z₀ : Fin 0 → ℂ) :
    boundaryIntegral Ω_0 f φ y = f z₀ := by
  have h_eq_arg : ∀ x : Fin 0 → ℝ, (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I) = z₀ := by
    intro x
    ext i
    exact Fin.elim0 i
  have h_meas : (volume : Measure (Fin 0 → ℝ)) Set.univ = 1 := by
    change Measure.pi (fun _ => volume) Set.univ = 1
    rw [Measure.pi_univ]
    simp
  have h_real : (volume : Measure (Fin 0 → ℝ)).real Set.univ = 1 := by
    dsimp [Measure.real]
    rw [h_meas]
    rfl
  dsimp [boundaryIntegral]
  have h_integrand :
      (fun x : Fin 0 → ℝ => f (fun i => (x i : ℂ) + (y i : ℂ) * Complex.I) * (φ x : ℂ)) =
        fun _ => f z₀ := by
    ext x
    rw [h_eq_arg x, hφ x, Complex.ofReal_one, mul_one]
  rw [h_integrand]
  simp only [integral_const]
  rw [h_real, one_smul]

lemma tendsto_const_nhdsWithin_zero {E F : Type*} [TopologicalSpace E] [TopologicalSpace F]
    [T1Space F] {s : Set E} (x : E) (hx : x ∈ s) {c L : F}
    (h_lim : Filter.Tendsto (fun _ : E => c) (nhdsWithin x s) (nhds L)) :
    c = L := by
  haveI : (nhdsWithin x s).NeBot := nhdsWithin_neBot_of_mem hx
  exact tendsto_const_nhds_iff.mp h_lim

lemma local_eow_epstein_zero
    (V_plus V_minus : Set (Fin n → ℝ))
    (h_opposite : V_minus = (fun y => -y) '' V_plus)
    (f_plus : (Fin n → ℂ) → ℂ)
    (f_minus : (Fin n → ℂ) → ℂ)
    (hf_plus_holo : DifferentiableOn ℂ f_plus (TubeDomain V_plus))
    (hf_minus_holo : DifferentiableOn ℂ f_minus (TubeDomain V_minus))
    (T_plus : 𝓓'(Ω_n, ℂ)) (hT_plus : HasBoundaryValue Ω_n f_plus V_plus T_plus)
    (T_minus : 𝓓'(Ω_n, ℂ)) (hT_minus : HasBoundaryValue Ω_n f_minus V_minus T_minus)
    (U : Opens (Fin n → ℝ)) (hU : (U : Set (Fin n → ℝ)) ⊆ Ω_n)
    (h_match : EqualOn Ω_n T_plus T_minus U hU)
    (hn : n = 0) :
    ∃ (W : Opens (Fin n → ℂ)) (F : (Fin n → ℂ) → ℂ),
      (∀ x ∈ U, (fun i => (x i : ℂ)) ∈ W) ∧
      DifferentiableOn ℂ F (W : Set (Fin n → ℂ)) ∧
      EqOn F f_plus ((W : Set (Fin n → ℂ)) ∩ TubeDomain V_plus) ∧
      EqOn F f_minus ((W : Set (Fin n → ℂ)) ∩ TubeDomain V_minus) := by
  by_cases hU_empty : (U : Set (Fin n → ℝ)) = ∅
  · exact local_eow_epstein_empty V_plus V_minus f_plus f_minus U hU_empty
  · have h_subsingleton : Subsingleton (Fin n → ℂ) := by
      subst hn
      infer_instance
    have h_subsingleton_R : Subsingleton (Fin n → ℝ) := by
      subst hn
      infer_instance
    have h_all_R : ∀ a b : Fin n → ℝ, a = b := fun a b => Subsingleton.elim a b
    have h_all_C : ∀ a b : Fin n → ℂ, a = b := fun a b => Subsingleton.elim a b
    by_cases h_plus : (TubeDomain V_plus).Nonempty
    · rcases h_plus with ⟨z₀, hz₀⟩
      have hz₀_im : (fun i => (z₀ i).im) ∈ V_plus := hz₀
      have h_zero_in_Vp : (0 : Fin n → ℝ) ∈ V_plus := by
        have : (0 : Fin n → ℝ) = (fun i => (z₀ i).im) := h_all_R 0 _
        rw [this]
        exact hz₀_im
      have h_zero_in_Vm : (0 : Fin n → ℝ) ∈ V_minus := by
        rw [h_opposite]
        exact ⟨0, h_zero_in_Vp, by ext i; exact Fin.elim0 (hn ▸ i)⟩
      have h_eq_vals : f_plus z₀ = f_minus z₀ := by
        subst hn
        have hU_univ : (U : Set (Fin 0 → ℝ)) = Set.univ := by
          ext x
          simp only [Set.mem_univ, iff_true]
          rcases Set.nonempty_iff_ne_empty.mpr hU_empty with ⟨x₀, hx₀⟩
          have : x = x₀ := Subsingleton.elim x x₀
          rw [this]
          exact hx₀
        have hΩ_univ : (Ω_n : Set (Fin 0 → ℝ)) = Set.univ := by
          ext x
          simp only [Set.mem_univ, iff_true]
          exact hU (by rw [hU_univ]; exact Set.mem_univ x)
        rcases exists_test_function_one Ω_n hΩ_univ with ⟨φ, hφ_one, _⟩
        have h_int_plus : ∀ y, boundaryIntegral Ω_n f_plus φ y = f_plus z₀ := by
          intro y
          exact boundaryIntegral_zero_dim Ω_n f_plus φ hφ_one y z₀
        have h_int_minus : ∀ y, boundaryIntegral Ω_n f_minus φ y = f_minus z₀ := by
          intro y
          exact boundaryIntegral_zero_dim Ω_n f_minus φ hφ_one y z₀
        have h_fun_plus : boundaryIntegral Ω_n f_plus φ = fun _ => f_plus z₀ := by
          ext y; exact h_int_plus y
        have h_fun_minus : boundaryIntegral Ω_n f_minus φ = fun _ => f_minus z₀ := by
          ext y; exact h_int_minus y
        have h_lim_plus := hT_plus φ
        have h_lim_minus := hT_minus φ
        rw [h_fun_plus] at h_lim_plus
        rw [h_fun_minus] at h_lim_minus
        have h_val_plus : f_plus z₀ = T_plus φ :=
          tendsto_const_nhdsWithin_zero 0 h_zero_in_Vp h_lim_plus
        have h_val_minus : f_minus z₀ = T_minus φ :=
          tendsto_const_nhdsWithin_zero 0 h_zero_in_Vm h_lim_minus
        have h_tsupp_U : tsupport (fun x => φ x) ⊆ (U : Set (Fin 0 → ℝ)) := by
          rw [hU_univ]
          exact subset_univ _
        have h_match_phi := h_match φ h_tsupp_U
        rw [h_val_plus, h_val_minus, h_match_phi]
      refine ⟨⊤, fun _ => f_plus z₀, ?_, ?_, ?_, ?_⟩
      · intro x hx; trivial
      · exact differentiable_const (f_plus z₀) |>.differentiableOn
      · intro z _
        rw [h_all_C z z₀]
      · intro z _
        rw [h_all_C z z₀, h_eq_vals]
    · refine ⟨⊤, fun _ => 0, ?_, ?_, ?_, ?_⟩
      · intro x hx; trivial
      · exact differentiable_const 0 |>.differentiableOn
      · intro z hz
        exact False.elim (h_plus ⟨z, hz.2⟩)
      · intro z hz
        have hz_minus : (fun i => (z i).im) ∈ V_minus := hz.2
        rw [h_opposite] at hz_minus
        rcases hz_minus with ⟨y', hy', _⟩
        have hz_plus : (TubeDomain V_plus).Nonempty := by
          refine ⟨0, ?_⟩
          have h_eq : (fun i : Fin n => ((0 : Fin n → ℂ) i).im) = y' := h_all_R _ _
          dsimp only [TubeDomain, mem_setOf_eq]
          rw [h_eq]
          exact hy'
        exact False.elim (h_plus hz_plus)

inductive EOWCoverIdx (U : Set (Fin n → ℝ))
  | plus : EOWCoverIdx U
  | minus : EOWCoverIdx U
  | loc (x : U) : EOWCoverIdx U

def eowCoverSet (V_plus V_minus : Set (Fin n → ℝ)) (U : Set (Fin n → ℝ))
    (r : (Fin n → ℝ) → ℝ) : EOWCoverIdx U → Set (Fin n → ℂ)
  | .plus => TubeDomain V_plus
  | .minus => TubeDomain V_minus
  | .loc ⟨x, _hx⟩ => Metric.ball (fun i => (x i : ℂ)) (r x)

def eowCoverFun (U : Set (Fin n → ℝ))
    (f_plus f_minus : (Fin n → ℂ) → ℂ)
    (F_loc : (Fin n → ℝ) → (Fin n → ℂ) → ℂ) :
    EOWCoverIdx U → (Fin n → ℂ) → ℂ
  | .plus => f_plus
  | .minus => f_minus
  | .loc ⟨x, _hx⟩ => F_loc x

lemma isOpen_eowCoverSet (V_plus V_minus : Set (Fin n → ℝ)) (U : Set (Fin n → ℝ))
    (hVp : IsOpen V_plus) (hVm : IsOpen V_minus)
    (r : (Fin n → ℝ) → ℝ) (i : EOWCoverIdx U) :
    IsOpen (eowCoverSet V_plus V_minus U r i) := by
  cases i with
  | plus => exact isOpen_TubeDomain hVp
  | minus => exact isOpen_TubeDomain hVm
  | loc x => exact Metric.isOpen_ball

lemma local_eow_glue (V_plus V_minus : Set (Fin n → ℝ)) (U : Opens (Fin n → ℝ))
    (hVp : IsOpen V_plus) (hVm : IsOpen V_minus)
    (h_disj : Disjoint (TubeDomain V_plus) (TubeDomain V_minus))
    (f_plus f_minus : (Fin n → ℂ) → ℂ)
    (hf_plus : DifferentiableOn ℂ f_plus (TubeDomain V_plus))
    (hf_minus : DifferentiableOn ℂ f_minus (TubeDomain V_minus))
    (r : (Fin n → ℝ) → ℝ) (hr : ∀ x ∈ (U : Set (Fin n → ℝ)), 0 < r x)
    (F_loc : (Fin n → ℝ) → (Fin n → ℂ) → ℂ)
    (hF_holo : ∀ x ∈ (U : Set (Fin n → ℝ)),
      DifferentiableOn ℂ (F_loc x) (Metric.ball (fun i => (x i : ℂ)) (r x)))
    (hF_eq_plus : ∀ x ∈ (U : Set (Fin n → ℝ)),
      EqOn (F_loc x) f_plus (Metric.ball (fun i => (x i : ℂ)) (r x) ∩ TubeDomain V_plus))
    (hF_eq_minus : ∀ x ∈ (U : Set (Fin n → ℝ)),
      EqOn (F_loc x) f_minus (Metric.ball (fun i => (x i : ℂ)) (r x) ∩ TubeDomain V_minus))
    (hF_compat : ∀ (x y : (U : Set (Fin n → ℝ))),
      EqOn (F_loc x.1) (F_loc y.1)
        (Metric.ball (fun i => (x.1 i : ℂ)) (r x.1) ∩
         Metric.ball (fun i => (y.1 i : ℂ)) (r y.1))) :
    ∃ (W : Opens (Fin n → ℂ)) (F : (Fin n → ℂ) → ℂ),
      (∀ x ∈ U, (fun i => (x i : ℂ)) ∈ W) ∧
      DifferentiableOn ℂ F (W : Set (Fin n → ℂ)) ∧
      EqOn F f_plus ((W : Set (Fin n → ℂ)) ∩ TubeDomain V_plus) ∧
      EqOn F f_minus ((W : Set (Fin n → ℂ)) ∩ TubeDomain V_minus) := by
  have hs_open : ∀ i : EOWCoverIdx (U : Set (Fin n → ℝ)),
      IsOpen (eowCoverSet V_plus V_minus (U : Set (Fin n → ℝ)) r i) :=
    isOpen_eowCoverSet V_plus V_minus U hVp hVm r
  have h_diff : ∀ i : EOWCoverIdx (U : Set (Fin n → ℝ)),
      DifferentiableOn ℂ (eowCoverFun (U : Set (Fin n → ℝ)) f_plus f_minus F_loc i)
        (eowCoverSet V_plus V_minus (U : Set (Fin n → ℝ)) r i) := by
    intro i
    cases i with
    | plus => exact hf_plus
    | minus => exact hf_minus
    | loc x => exact hF_holo x.1 x.2
  have h_compat : ∀ i j : EOWCoverIdx (U : Set (Fin n → ℝ)),
      EqOn (eowCoverFun (U : Set (Fin n → ℝ)) f_plus f_minus F_loc i)
           (eowCoverFun (U : Set (Fin n → ℝ)) f_plus f_minus F_loc j)
           (eowCoverSet V_plus V_minus (U : Set (Fin n → ℝ)) r i ∩
            eowCoverSet V_plus V_minus (U : Set (Fin n → ℝ)) r j) := by
    intro i j z hz
    cases i with
    | plus =>
      cases j with
      | plus => rfl
      | minus =>
        have h_inter : z ∈ TubeDomain V_plus ∩ TubeDomain V_minus := hz
        exact False.elim (Set.disjoint_iff.mp h_disj h_inter)
      | loc x =>
        exact (hF_eq_plus x.1 x.2 ⟨hz.2, hz.1⟩).symm
    | minus =>
      cases j with
      | plus =>
        have h_inter : z ∈ TubeDomain V_plus ∩ TubeDomain V_minus := ⟨hz.2, hz.1⟩
        exact False.elim (Set.disjoint_iff.mp h_disj h_inter)
      | minus => rfl
      | loc x =>
        exact (hF_eq_minus x.1 x.2 ⟨hz.2, hz.1⟩).symm
    | loc x =>
      cases j with
      | plus => exact hF_eq_plus x.1 x.2 ⟨hz.1, hz.2⟩
      | minus => exact hF_eq_minus x.1 x.2 ⟨hz.1, hz.2⟩
      | loc y => exact hF_compat x y hz
  rcases differentiableOn_iUnion_of_locally_differentiable
    (eowCoverSet V_plus V_minus (U : Set (Fin n → ℝ)) r) hs_open
    (eowCoverFun (U : Set (Fin n → ℝ)) f_plus f_minus F_loc) h_diff h_compat with
    ⟨F, hF_diff, hF_eq_i⟩
  let W_set := ⋃ i, eowCoverSet V_plus V_minus (U : Set (Fin n → ℝ)) r i
  have hW_open : IsOpen W_set := isOpen_iUnion hs_open
  let W : Opens (Fin n → ℂ) := ⟨W_set, hW_open⟩
  refine ⟨W, F, ?_, hF_diff, ?_, ?_⟩
  · intro x hx
    exact mem_iUnion.2 ⟨.loc ⟨x, hx⟩, Metric.mem_ball_self (hr x hx)⟩
  · intro z hz
    have hz_W : z ∈ eowCoverSet V_plus V_minus (U : Set (Fin n → ℝ)) r .plus := hz.2
    exact hF_eq_i .plus hz_W
  · intro z hz
    have hz_W : z ∈ eowCoverSet V_plus V_minus (U : Set (Fin n → ℝ)) r .minus := hz.2
    exact hF_eq_i .minus hz_W

structure LocalEpsteinData
    (V_plus V_minus : Set (Fin n → ℝ))
    (f_plus f_minus : (Fin n → ℂ) → ℂ)
    (x : Fin n → ℝ) where
  r : ℝ
  hr : 0 < r
  F : (Fin n → ℂ) → ℂ
  hF_diff : DifferentiableOn ℂ F (Metric.ball (fun i => (x i : ℂ)) r)
  hF_plus : EqOn F f_plus (Metric.ball (fun i => (x i : ℂ)) r ∩ TubeDomain V_plus)
  hF_minus : EqOn F f_minus (Metric.ball (fun i => (x i : ℂ)) r ∩ TubeDomain V_minus)

lemma norm_im_le_norm_sub_real (z : Fin n → ℂ) (x : Fin n → ℝ) :
    ‖fun i => (z i).im‖ ≤ ‖z - (fun i => (x i : ℂ))‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro i
  have h1 : (z i).im = ((z - (fun i => (x i : ℂ))) i).im := by
    simp only [Pi.sub_apply, Complex.sub_im, Complex.ofReal_im, sub_zero]
  rw [h1]
  have h2 : ‖((z - (fun i => (x i : ℂ))) i).im‖ ≤ ‖(z - (fun i => (x i : ℂ))) i‖ := by
    rw [Real.norm_eq_abs]
    exact Complex.abs_im_le_norm _
  exact h2.trans (norm_le_pi_norm (z - (fun i => (x i : ℂ))) i)

lemma local_eow_glue_balls (V_plus V_minus : Set (Fin n → ℝ)) (U : Opens (Fin n → ℝ))
    (f_plus f_minus : (Fin n → ℂ) → ℂ)
    (r : (Fin n → ℝ) → ℝ) (hr : ∀ x ∈ (U : Set (Fin n → ℝ)), 0 < r x)
    (F_loc : (Fin n → ℝ) → (Fin n → ℂ) → ℂ)
    (hF_holo : ∀ x ∈ (U : Set (Fin n → ℝ)),
      DifferentiableOn ℂ (F_loc x) (Metric.ball (fun i => (x i : ℂ)) (r x)))
    (hF_eq_plus : ∀ x ∈ (U : Set (Fin n → ℝ)),
      EqOn (F_loc x) f_plus (Metric.ball (fun i => (x i : ℂ)) (r x) ∩ TubeDomain V_plus))
    (hF_eq_minus : ∀ x ∈ (U : Set (Fin n → ℝ)),
      EqOn (F_loc x) f_minus (Metric.ball (fun i => (x i : ℂ)) (r x) ∩ TubeDomain V_minus))
    (hF_compat : ∀ (x y : {x // x ∈ (U : Set (Fin n → ℝ))}),
      EqOn (F_loc x.1) (F_loc y.1)
        (Metric.ball (fun i => (x.1 i : ℂ)) (r x.1) ∩
         Metric.ball (fun i => (y.1 i : ℂ)) (r y.1))) :
    ∃ (W : Opens (Fin n → ℂ)) (F : (Fin n → ℂ) → ℂ),
      (∀ x ∈ U, (fun i => (x i : ℂ)) ∈ W) ∧
      DifferentiableOn ℂ F (W : Set (Fin n → ℂ)) ∧
      EqOn F f_plus ((W : Set (Fin n → ℂ)) ∩ TubeDomain V_plus) ∧
      EqOn F f_minus ((W : Set (Fin n → ℂ)) ∩ TubeDomain V_minus) := by
  let ball_set : {x // x ∈ (U : Set (Fin n → ℝ))} → Set (Fin n → ℂ) :=
    fun x => Metric.ball (fun i => (x.1 i : ℂ)) (r x.1)
  have hs_open : ∀ x : {x // x ∈ (U : Set (Fin n → ℝ))}, IsOpen (ball_set x) :=
    fun _ => Metric.isOpen_ball
  have h_diff : ∀ x : {x // x ∈ (U : Set (Fin n → ℝ))},
      DifferentiableOn ℂ (F_loc x.1) (ball_set x) :=
    fun x => hF_holo x.1 x.2
  have h_compat : ∀ x y : {x // x ∈ (U : Set (Fin n → ℝ))},
      EqOn (F_loc x.1) (F_loc y.1) (ball_set x ∩ ball_set y) :=
    fun x y => hF_compat x y
  rcases differentiableOn_iUnion_of_locally_differentiable
    ball_set hs_open (fun x => F_loc x.1) h_diff h_compat with ⟨F, hF_diff, hF_eq_i⟩
  let W_set := ⋃ x : {x // x ∈ (U : Set (Fin n → ℝ))}, ball_set x
  have hW_open : IsOpen W_set := isOpen_iUnion hs_open
  let W : Opens (Fin n → ℂ) := ⟨W_set, hW_open⟩
  have hF_diff' : DifferentiableOn ℂ F (W : Set (Fin n → ℂ)) := hF_diff
  refine ⟨W, F, ?_, hF_diff', ?_, ?_⟩
  · intro x hx
    exact mem_iUnion.2 ⟨⟨x, hx⟩, Metric.mem_ball_self (hr x hx)⟩
  · intro z hz
    rcases mem_iUnion.1 hz.1 with ⟨x, hzx⟩
    have hF_eq := hF_eq_i x hzx
    have hF_plus := hF_eq_plus x.1 x.2 ⟨hzx, hz.2⟩
    rw [hF_eq, hF_plus]
  · intro z hz
    rcases mem_iUnion.1 hz.1 with ⟨x, hzx⟩
    have hF_eq := hF_eq_i x hzx
    have hF_minus := hF_eq_minus x.1 x.2 ⟨hzx, hz.2⟩
    rw [hF_eq, hF_minus]

lemma local_eow_epstein_from_data
    (V_plus V_minus : Set (Fin n → ℝ))
    (f_plus f_minus : (Fin n → ℂ) → ℂ)
    (U : Opens (Fin n → ℝ))
    (data : ∀ x ∈ (U : Set (Fin n → ℝ)), LocalEpsteinData V_plus V_minus f_plus f_minus x)
    (h_compat : ∀ (x y : {x // x ∈ (U : Set (Fin n → ℝ))}),
      EqOn (data x.1 x.2).F (data y.1 y.2).F
        (Metric.ball (fun i => (x.1 i : ℂ)) (data x.1 x.2).r ∩
         Metric.ball (fun i => (y.1 i : ℂ)) (data y.1 y.2).r)) :
    ∃ (W : Opens (Fin n → ℂ)) (F : (Fin n → ℂ) → ℂ),
      (∀ x ∈ U, (fun i => (x i : ℂ)) ∈ W) ∧
      DifferentiableOn ℂ F (W : Set (Fin n → ℂ)) ∧
      EqOn F f_plus ((W : Set (Fin n → ℂ)) ∩ TubeDomain V_plus) ∧
      EqOn F f_minus ((W : Set (Fin n → ℂ)) ∩ TubeDomain V_minus) := by
  classical
  let r : (Fin n → ℝ) → ℝ := fun x =>
    if hx : x ∈ (U : Set (Fin n → ℝ)) then (data x hx).r else 1
  let F_loc : (Fin n → ℝ) → (Fin n → ℂ) → ℂ := fun x =>
    if hx : x ∈ (U : Set (Fin n → ℝ)) then (data x hx).F else 0
  have hr_pos : ∀ x ∈ (U : Set (Fin n → ℝ)), 0 < r x := by
    intro x hx
    dsimp [r]
    rw [dif_pos hx]
    exact (data x hx).hr
  have hF_holo : ∀ x ∈ (U : Set (Fin n → ℝ)),
      DifferentiableOn ℂ (F_loc x) (Metric.ball (fun i => (x i : ℂ)) (r x)) := by
    intro x hx
    dsimp [F_loc, r]
    rw [dif_pos hx, dif_pos hx]
    exact (data x hx).hF_diff
  have hF_plus : ∀ x ∈ (U : Set (Fin n → ℝ)),
      EqOn (F_loc x) f_plus (Metric.ball (fun i => (x i : ℂ)) (r x) ∩ TubeDomain V_plus) := by
    intro x hx
    dsimp [F_loc, r]
    rw [dif_pos hx, dif_pos hx]
    exact (data x hx).hF_plus
  have hF_minus : ∀ x ∈ (U : Set (Fin n → ℝ)),
      EqOn (F_loc x) f_minus (Metric.ball (fun i => (x i : ℂ)) (r x) ∩ TubeDomain V_minus) := by
    intro x hx
    dsimp [F_loc, r]
    rw [dif_pos hx, dif_pos hx]
    exact (data x hx).hF_minus
  have hF_c : ∀ (x y : {x // x ∈ (U : Set (Fin n → ℝ))}),
      EqOn (F_loc x.1) (F_loc y.1)
        (Metric.ball (fun i => (x.1 i : ℂ)) (r x.1) ∩
         Metric.ball (fun i => (y.1 i : ℂ)) (r y.1)) := by
    intro x y
    dsimp [F_loc, r]
    rw [dif_pos x.2, dif_pos x.2, dif_pos y.2, dif_pos y.2]
    exact h_compat x y
  exact local_eow_glue_balls V_plus V_minus U f_plus f_minus r hr_pos F_loc
    hF_holo hF_plus hF_minus hF_c

lemma local_eow_epstein_case_not_in_closure
    (V_plus V_minus : Set (Fin n → ℝ))
    (h_opposite : V_minus = (fun y => -y) '' V_plus)
    (f_plus : (Fin n → ℂ) → ℂ)
    (f_minus : (Fin n → ℂ) → ℂ)
    (U : Opens (Fin n → ℝ))
    (h0 : (0 : Fin n → ℝ) ∉ closure V_plus) :
    ∃ (W : Opens (Fin n → ℂ)) (F : (Fin n → ℂ) → ℂ),
      (∀ x ∈ U, (fun i => (x i : ℂ)) ∈ W) ∧
      DifferentiableOn ℂ F (W : Set (Fin n → ℂ)) ∧
      EqOn F f_plus ((W : Set (Fin n → ℂ)) ∩ TubeDomain V_plus) ∧
      EqOn F f_minus ((W : Set (Fin n → ℂ)) ∩ TubeDomain V_minus) := by
  rw [Metric.mem_closure_iff] at h0
  push Not at h0
  rcases h0 with ⟨δ, hδ_pos, hδ_disj⟩
  let W_set := ⋃ x : {x // x ∈ (U : Set (Fin n → ℝ))}, Metric.ball (fun i => (x.1 i : ℂ)) δ
  have hW_open : IsOpen W_set := isOpen_iUnion (fun _ => Metric.isOpen_ball)
  let W : Opens (Fin n → ℂ) := ⟨W_set, hW_open⟩
  have hW_disj_plus : (W : Set (Fin n → ℂ)) ∩ TubeDomain V_plus = ∅ := by
    ext z
    simp only [mem_inter_iff, mem_empty_iff_false, iff_false]
    rintro ⟨hz1, hz2⟩
    rcases mem_iUnion.1 hz1 with ⟨⟨x, hxU⟩, hzx⟩
    have hz_tube : (fun i => (z i).im) ∈ V_plus := hz2
    have h_dist : ‖fun i => (z i).im‖ < δ := by
      have := norm_im_le_norm_sub_real z x
      have h_ball : ‖z - (fun i => (x i : ℂ))‖ < δ := by
        rw [← dist_eq_norm]
        exact Metric.mem_ball.1 hzx
      exact this.trans_lt h_ball
    have h_le := hδ_disj (fun i => (z i).im) hz_tube
    rw [dist_zero_left] at h_le
    linarith
  have hW_disj_minus : (W : Set (Fin n → ℂ)) ∩ TubeDomain V_minus = ∅ := by
    ext z
    simp only [mem_inter_iff, mem_empty_iff_false, iff_false]
    rintro ⟨hz1, hz2⟩
    rcases mem_iUnion.1 hz1 with ⟨⟨x, hxU⟩, hzx⟩
    have hz_tube : (fun i => (z i).im) ∈ V_minus := hz2
    rw [h_opposite] at hz_tube
    rcases hz_tube with ⟨y, hy, hy_eq⟩
    dsimp at hy_eq
    have h_dist : ‖fun i => (z i).im‖ < δ := by
      have := norm_im_le_norm_sub_real z x
      have h_ball : ‖z - (fun i => (x i : ℂ))‖ < δ := by
        rw [← dist_eq_norm]
        exact Metric.mem_ball.1 hzx
      exact this.trans_lt h_ball
    have h_norm_y : ‖y‖ < δ := by
      have h_neg : ‖-y‖ = ‖y‖ := norm_neg y
      rw [← h_neg, hy_eq]
      exact h_dist
    have h_le := hδ_disj y hy
    rw [dist_zero_left] at h_le
    linarith
  refine ⟨W, fun _ => 0, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact mem_iUnion.2 ⟨⟨x, hx⟩, Metric.mem_ball_self hδ_pos⟩
  · exact differentiable_const 0 |>.differentiableOn
  · rw [hW_disj_plus]
    exact eqOn_empty _ _
  · rw [hW_disj_minus]
    exact eqOn_empty _ _

lemma local_epstein_extension_of_common_F
    (V_plus V_minus : Set (Fin n → ℝ))
    (f_plus : (Fin n → ℂ) → ℂ)
    (f_minus : (Fin n → ℂ) → ℂ)
    (U : Opens (Fin n → ℝ))
    (r : (Fin n → ℝ) → ℝ) (hr : ∀ x ∈ (U : Set (Fin n → ℝ)), 0 < r x)
    (F : (Fin n → ℂ) → ℂ)
    (hF_diff : ∀ x ∈ (U : Set (Fin n → ℝ)),
      DifferentiableOn ℂ F (Metric.ball (fun i => (x i : ℂ)) (r x)))
    (hF_plus : ∀ x ∈ (U : Set (Fin n → ℝ)),
      EqOn F f_plus (Metric.ball (fun i => (x i : ℂ)) (r x) ∩ TubeDomain V_plus))
    (hF_minus : ∀ x ∈ (U : Set (Fin n → ℝ)),
      EqOn F f_minus (Metric.ball (fun i => (x i : ℂ)) (r x) ∩ TubeDomain V_minus)) :
    ∃ (W : Opens (Fin n → ℂ)) (F_ext : (Fin n → ℂ) → ℂ),
      (∀ x ∈ U, (fun i => (x i : ℂ)) ∈ W) ∧
      DifferentiableOn ℂ F_ext (W : Set (Fin n → ℂ)) ∧
      EqOn F_ext f_plus ((W : Set (Fin n → ℂ)) ∩ TubeDomain V_plus) ∧
      EqOn F_ext f_minus ((W : Set (Fin n → ℂ)) ∩ TubeDomain V_minus) := by
  have h_compat : ∀ (x y : {x // x ∈ (U : Set (Fin n → ℝ))}),
      EqOn F F
        (Metric.ball (fun i => (x.1 i : ℂ)) (r x.1) ∩
         Metric.ball (fun i => (y.1 i : ℂ)) (r y.1)) := by
    intro x y z hz
    rfl
  exact local_eow_glue_balls V_plus V_minus U f_plus f_minus r hr
    (fun _ => F) hF_diff hF_plus hF_minus h_compat

def localEpsteinData_of_open_matches
    (V_plus V_minus : Set (Fin n → ℝ))
    (hV_plus_open : IsOpen V_plus) (hV_plus_conv : Convex ℝ V_plus)
    (hV_minus_open : IsOpen V_minus) (hV_minus_conv : Convex ℝ V_minus)
    (f_plus : (Fin n → ℂ) → ℂ)
    (f_minus : (Fin n → ℂ) → ℂ)
    (hf_plus_holo : DifferentiableOn ℂ f_plus (TubeDomain V_plus))
    (hf_minus_holo : DifferentiableOn ℂ f_minus (TubeDomain V_minus))
    (x : Fin n → ℝ)
    (ρ : ℝ) (hρ : 0 < ρ)
    (F : (Fin n → ℂ) → ℂ)
    (hF_diff : DifferentiableOn ℂ F (Metric.ball (fun i => (x i : ℂ)) ρ))
    (W₁ : Set (Fin n → ℂ)) (hW₁_open : IsOpen W₁) (hW₁_ne : W₁.Nonempty)
    (hW₁_sub : W₁ ⊆ Metric.ball (fun i => (x i : ℂ)) ρ ∩ TubeDomain V_plus)
    (hF_eq1 : EqOn F f_plus W₁)
    (W₂ : Set (Fin n → ℂ)) (hW₂_open : IsOpen W₂) (hW₂_ne : W₂.Nonempty)
    (hW₂_sub : W₂ ⊆ Metric.ball (fun i => (x i : ℂ)) ρ ∩ TubeDomain V_minus)
    (hF_eq2 : EqOn F f_minus W₂) :
    LocalEpsteinData V_plus V_minus f_plus f_minus x := by
  have hB_open : IsOpen (Metric.ball (fun i => (x i : ℂ)) ρ) := Metric.isOpen_ball
  have hB_conv : Convex ℝ (Metric.ball (fun i => (x i : ℂ)) ρ) := convex_ball _ _
  have hT_plus_open : IsOpen (TubeDomain V_plus) := isOpen_TubeDomain hV_plus_open
  have hT_minus_open : IsOpen (TubeDomain V_minus) := isOpen_TubeDomain hV_minus_open
  have hT_plus_conv : Convex ℝ (TubeDomain V_plus) := convex_TubeDomain hV_plus_conv
  have hT_minus_conv : Convex ℝ (TubeDomain V_minus) := convex_TubeDomain hV_minus_conv
  let S₁ := Metric.ball (fun i => (x i : ℂ)) ρ ∩ TubeDomain V_plus
  have hS₁_open : IsOpen S₁ := hB_open.inter hT_plus_open
  have hS₁_conv : Convex ℝ S₁ := hB_conv.inter hT_plus_conv
  have hd₁ : DifferentiableOn ℂ (F - f_plus) S₁ :=
    (hF_diff.mono inter_subset_left).sub (hf_plus_holo.mono inter_subset_right)
  have h_zero1 : EqOn (F - f_plus) 0 S₁ := by
    apply eqOn_zero_of_convex_differentiableOn hS₁_open hS₁_conv hd₁ hW₁_open hW₁_sub hW₁_ne
    intro z hz
    simp only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero]
    exact hF_eq1 hz
  have hF_plus : EqOn F f_plus S₁ := by
    intro z hz
    have := h_zero1 hz
    simp only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at this
    exact this
  let S₂ := Metric.ball (fun i => (x i : ℂ)) ρ ∩ TubeDomain V_minus
  have hS₂_open : IsOpen S₂ := hB_open.inter hT_minus_open
  have hS₂_conv : Convex ℝ S₂ := hB_conv.inter hT_minus_conv
  have hd₂ : DifferentiableOn ℂ (F - f_minus) S₂ :=
    (hF_diff.mono inter_subset_left).sub (hf_minus_holo.mono inter_subset_right)
  have h_zero2 : EqOn (F - f_minus) 0 S₂ := by
    apply eqOn_zero_of_convex_differentiableOn hS₂_open hS₂_conv hd₂ hW₂_open hW₂_sub hW₂_ne
    intro z hz
    simp only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero]
    exact hF_eq2 hz
  have hF_minus : EqOn F f_minus S₂ := by
    intro z hz
    have := h_zero2 hz
    simp only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at this
    exact this
  exact ⟨ρ, hρ, F, hF_diff, hF_plus, hF_minus⟩

lemma isOpen_neg_image {s : Set (Fin n → ℝ)} (hs : IsOpen s) :
    IsOpen ((fun v => -v) '' s) := by
  have : ((fun v => -v) '' s) = (fun v => -v) ⁻¹' s := by
    ext v; simp
  rw [this]
  exact hs.preimage continuous_neg

lemma convex_neg_image {s : Set (Fin n → ℝ)} (hs : Convex ℝ s) :
    Convex ℝ ((fun v => -v) '' s) := by
  rintro _ ⟨v₁, hv₁, rfl⟩ _ ⟨v₂, hv₂, rfl⟩ a b ha hb hab
  exact ⟨a • v₁ + b • v₂, hs hv₁ hv₂ ha hb hab, by simp [add_comm]⟩

noncomputable def localEpsteinData_of_core
    (V_plus : Set (Fin n → ℝ))
    (hV_plus_open : IsOpen V_plus) (hV_plus_conv : Convex ℝ V_plus)
    (f : (Fin n → ℂ) → ℂ)
    (hf_plus_holo : DifferentiableOn ℂ f (TubeDomain V_plus))
    (hf_minus_holo : DifferentiableOn ℂ f (TubeDomain ((fun v : Fin n → ℝ => -v) '' V_plus)))
    (x : Fin n → ℝ)
    (h_core : LocalEOWCore V_plus f x) :
    LocalEpsteinData V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) f f x := by
  have h_ex :
      ∃ (d : LocalEpsteinData V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) f f x),
        True := by
    obtain ⟨ρ, hρ, F, hF_an, ⟨W₁, hW₁o, hW₁n, hW₁s, hW₁e⟩, ⟨W₂, hW₂o, hW₂n, hW₂s, hW₂e⟩⟩ := h_core
    have hVm_conv : Convex ℝ ((fun v : Fin n → ℝ => -v) '' V_plus) := convex_neg_image hV_plus_conv
    have hVm_open : IsOpen ((fun v : Fin n → ℝ => -v) '' V_plus) := isOpen_neg_image hV_plus_open
    exact ⟨localEpsteinData_of_open_matches V_plus ((fun v : Fin n → ℝ => -v) '' V_plus)
      hV_plus_open hV_plus_conv hVm_open hVm_conv
      f f hf_plus_holo hf_minus_holo x ρ hρ F hF_an.differentiableOn
      W₁ hW₁o hW₁n hW₁s hW₁e W₂ hW₂o hW₂n hW₂s hW₂e, trivial⟩
  exact Classical.choose h_ex

def localEpsteinData_of_disjoint
    (V_plus V_minus : Set (Fin n → ℝ))
    (f_plus f_minus : (Fin n → ℂ) → ℂ)
    (x : Fin n → ℝ)
    (ρ : ℝ) (hρ : 0 < ρ)
    (h_disj_plus : Metric.ball (fun i => (x i : ℂ)) ρ ∩ TubeDomain V_plus = ∅)
    (h_disj_minus : Metric.ball (fun i => (x i : ℂ)) ρ ∩ TubeDomain V_minus = ∅) :
    LocalEpsteinData V_plus V_minus f_plus f_minus x := by
  refine ⟨ρ, hρ, fun _ => 0, ?_, ?_, ?_⟩
  · exact differentiable_const 0 |>.differentiableOn
  · rw [h_disj_plus]
    exact eqOn_empty _ _
  · rw [h_disj_minus]
    exact eqOn_empty _ _

def localEpsteinData_shrink
    (V_plus V_minus : Set (Fin n → ℝ))
    (f_plus f_minus : (Fin n → ℂ) → ℂ)
    (x : Fin n → ℝ)
    (d : LocalEpsteinData V_plus V_minus f_plus f_minus x)
    (r' : ℝ) (hr'_pos : 0 < r') (hr'_le : r' ≤ d.r) :
    LocalEpsteinData V_plus V_minus f_plus f_minus x := by
  have h_sub : Metric.ball (fun i => (x i : ℂ)) r' ⊆ Metric.ball (fun i => (x i : ℂ)) d.r :=
    Metric.ball_subset_ball hr'_le
  refine ⟨r', hr'_pos, d.F, ?_, ?_, ?_⟩
  · exact d.hF_diff.mono h_sub
  · exact d.hF_plus.mono (inter_subset_inter_left _ h_sub)
  · exact d.hF_minus.mono (inter_subset_inter_left _ h_sub)

lemma localEpsteinData_compat_of_inter_nonempty
    (V_plus V_minus : Set (Fin n → ℝ))
    (hV_plus_open : IsOpen V_plus)
    (f_plus f_minus : (Fin n → ℂ) → ℂ)
    (x y : Fin n → ℝ)
    (dx : LocalEpsteinData V_plus V_minus f_plus f_minus x)
    (dy : LocalEpsteinData V_plus V_minus f_plus f_minus y)
    (h_inter_nonempty : (Metric.ball (fun i => (x i : ℂ)) dx.r ∩
                         Metric.ball (fun i => (y i : ℂ)) dy.r ∩
                         TubeDomain V_plus).Nonempty) :
    EqOn dx.F dy.F (Metric.ball (fun i => (x i : ℂ)) dx.r ∩
                    Metric.ball (fun i => (y i : ℂ)) dy.r) := by
  let B := Metric.ball (fun i => (x i : ℂ)) dx.r ∩ Metric.ball (fun i => (y i : ℂ)) dy.r
  have hB_open : IsOpen B := Metric.isOpen_ball.inter Metric.isOpen_ball
  have hB_conv : Convex ℝ B := (convex_ball _ _).inter (convex_ball _ _)
  have hd : DifferentiableOn ℂ (dx.F - dy.F) B :=
    (dx.hF_diff.mono inter_subset_left).sub (dy.hF_diff.mono inter_subset_right)
  let W := B ∩ TubeDomain V_plus
  have hW_open : IsOpen W := hB_open.inter (isOpen_TubeDomain hV_plus_open)
  have hW_sub : W ⊆ B := inter_subset_left
  have hW_eq : EqOn (dx.F - dy.F) 0 W := by
    intro z hz
    simp only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero]
    have hz_x : z ∈ Metric.ball (fun i => (x i : ℂ)) dx.r ∩ TubeDomain V_plus :=
      ⟨hz.1.1, hz.2⟩
    have hz_y : z ∈ Metric.ball (fun i => (y i : ℂ)) dy.r ∩ TubeDomain V_plus :=
      ⟨hz.1.2, hz.2⟩
    rw [dx.hF_plus hz_x, dy.hF_plus hz_y]
  have h_zero := eqOn_zero_of_convex_differentiableOn
    hB_open hB_conv hd hW_open hW_sub h_inter_nonempty hW_eq
  intro z hz
  have hz0 := h_zero hz
  simp only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at hz0
  exact hz0

lemma re_mem_ball_of_mem_ball (x : Fin n → ℝ) (r : ℝ) (z : Fin n → ℂ)
    (hz : z ∈ Metric.ball (fun i => (x i : ℂ)) r) :
    (fun i => (z i).re) ∈ Metric.ball x r := by
  rw [Metric.mem_ball, dist_eq_norm] at hz ⊢
  have hr_pos : 0 < r := (norm_nonneg _).trans_lt hz
  rw [pi_norm_lt_iff hr_pos] at hz ⊢
  intro i
  have h1 : ‖((fun i => (z i).re) - x) i‖ = |(z i).re - x i| := by
    simp only [Pi.sub_apply, Real.norm_eq_abs]
  have h2 : |(z i).re - x i| = |(z i - (x i : ℂ)).re| := by
    simp only [Complex.sub_re, Complex.ofReal_re]
  have h3 : |(z i - (x i : ℂ)).re| ≤ ‖(z - (fun i => (x i : ℂ))) i‖ := by
    simp only [Pi.sub_apply]
    exact Complex.abs_re_le_norm _
  rw [h1, h2]
  exact h3.trans_lt (hz i)

lemma re_mem_inter_balls (x y : Fin n → ℝ) (rx ry : ℝ) (z : Fin n → ℂ)
    (hz : z ∈ Metric.ball (fun i => (x i : ℂ)) rx ∩ Metric.ball (fun i => (y i : ℂ)) ry) :
    (fun i => (z i).re) ∈ Metric.ball x rx ∩ Metric.ball y ry :=
  ⟨re_mem_ball_of_mem_ball x rx z hz.1, re_mem_ball_of_mem_ball y ry z hz.2⟩

lemma norm_real_add_I_sub_le (p x u : Fin n → ℝ) :
    ‖(fun i => (p i : ℂ) + (u i : ℂ) * Complex.I) - (fun i => (x i : ℂ))‖ ≤
      ‖p - x‖ + ‖u‖ := by
  let z : Fin n → ℂ := fun i => (p i : ℂ) + (u i : ℂ) * Complex.I
  have h_comp : ∀ i, ‖(z - (fun i => (x i : ℂ))) i‖ ≤ ‖p - x‖ + ‖u‖ := by
    intro i
    have h_eq : (z - (fun i => (x i : ℂ))) i = ((p i - x i : ℝ) : ℂ) + (u i : ℂ) * Complex.I := by
      dsimp [z]
      push_cast
      ring
    rw [h_eq]
    have h_add := norm_add_le ((p i - x i : ℝ) : ℂ) ((u i : ℂ) * Complex.I)
    have h1 : ‖((p i - x i : ℝ) : ℂ)‖ = ‖p i - x i‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    have h2 : ‖(u i : ℂ) * Complex.I‖ = ‖u i‖ := by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    rw [h1, h2] at h_add
    have h_p_le : ‖p i - x i‖ ≤ ‖p - x‖ := by
      have : ‖p i - x i‖ = ‖(p - x) i‖ := by simp only [Pi.sub_apply]
      rw [this]
      exact norm_le_pi_norm (p - x) i
    have h_u_le : ‖u i‖ ≤ ‖u‖ := norm_le_pi_norm u i
    exact h_add.trans (add_le_add h_p_le h_u_le)
  have h_nonneg : 0 ≤ ‖p - x‖ + ‖u‖ := by positivity
  exact (pi_norm_le_iff_of_nonneg h_nonneg).mpr h_comp

lemma inter_balls_tube_nonempty_of_mem_inter_real
    (V_plus : Set (Fin n → ℝ)) (h0 : (0 : Fin n → ℝ) ∈ closure V_plus)
    (x y : Fin n → ℝ) (rx ry : ℝ)
    (p : Fin n → ℝ) (hp : p ∈ Metric.ball x rx ∩ Metric.ball y ry) :
    (Metric.ball (fun i => (x i : ℂ)) rx ∩ Metric.ball (fun i => (y i : ℂ)) ry ∩
     TubeDomain V_plus).Nonempty := by
  have hpx : ‖p - x‖ < rx := by
    rw [← dist_eq_norm]
    exact Metric.mem_ball.mp hp.1
  have hpy : ‖p - y‖ < ry := by
    rw [← dist_eq_norm]
    exact Metric.mem_ball.mp hp.2
  let δx := rx - ‖p - x‖
  let δy := ry - ‖p - y‖
  have hδx : 0 < δx := sub_pos.mpr hpx
  have hδy : 0 < δy := sub_pos.mpr hpy
  let δ := min δx δy
  have hδ : 0 < δ := lt_min hδx hδy
  rw [Metric.mem_closure_iff] at h0
  rcases h0 δ hδ with ⟨u, hu_V, hu_dist⟩
  have hu_norm : ‖u‖ < δ := by
    rw [dist_zero_left] at hu_dist
    exact hu_dist
  let z : Fin n → ℂ := fun i => (p i : ℂ) + (u i : ℂ) * Complex.I
  refine ⟨z, ⟨?_, ?_⟩, ?_⟩
  · rw [Metric.mem_ball, dist_eq_norm]
    have h_le := norm_real_add_I_sub_le p x u
    have h_lt : ‖p - x‖ + ‖u‖ < rx := by
      have : ‖u‖ < δx := hu_norm.trans_le (min_le_left _ _)
      linarith
    exact h_le.trans_lt h_lt
  · rw [Metric.mem_ball, dist_eq_norm]
    have h_le := norm_real_add_I_sub_le p y u
    have h_lt : ‖p - y‖ + ‖u‖ < ry := by
      have : ‖u‖ < δy := hu_norm.trans_le (min_le_right _ _)
      linarith
    exact h_le.trans_lt h_lt
  · dsimp [TubeDomain, mem_setOf_eq]
    have h_im : (fun i => (z i).im) = u := by
      ext i
      simp only [z, Complex.add_im, Complex.ofReal_im, Complex.mul_I_im, Complex.ofReal_re,
                 zero_add]
    rw [h_im]
    exact hu_V

lemma localEpsteinData_compat
    (V_plus V_minus : Set (Fin n → ℝ))
    (hV_plus_open : IsOpen V_plus)
    (h0 : (0 : Fin n → ℝ) ∈ closure V_plus)
    (f_plus f_minus : (Fin n → ℂ) → ℂ)
    (x y : Fin n → ℝ)
    (dx : LocalEpsteinData V_plus V_minus f_plus f_minus x)
    (dy : LocalEpsteinData V_plus V_minus f_plus f_minus y) :
    EqOn dx.F dy.F (Metric.ball (fun i => (x i : ℂ)) dx.r ∩
                    Metric.ball (fun i => (y i : ℂ)) dy.r) := by
  let B := Metric.ball (fun i => (x i : ℂ)) dx.r ∩ Metric.ball (fun i => (y i : ℂ)) dy.r
  by_cases h_inter : B.Nonempty
  · rcases h_inter with ⟨w, hw⟩
    let p : Fin n → ℝ := fun i => (w i).re
    have hp : p ∈ Metric.ball x dx.r ∩ Metric.ball y dy.r :=
      re_mem_inter_balls x y dx.r dy.r w hw
    have h_tube_nonempty : (B ∩ TubeDomain V_plus).Nonempty :=
      inter_balls_tube_nonempty_of_mem_inter_real V_plus h0 x y dx.r dy.r p hp
    exact localEpsteinData_compat_of_inter_nonempty V_plus V_minus hV_plus_open
      f_plus f_minus x y dx dy h_tube_nonempty
  · intro z hz
    exact False.elim (h_inter ⟨z, hz⟩)

lemma localEpsteinData_family_compat
    (V_plus V_minus : Set (Fin n → ℝ))
    (hV_plus_open : IsOpen V_plus)
    (h0 : (0 : Fin n → ℝ) ∈ closure V_plus)
    (f_plus f_minus : (Fin n → ℂ) → ℂ)
    (U : Opens (Fin n → ℝ))
    (data : ∀ x ∈ (U : Set (Fin n → ℝ)), LocalEpsteinData V_plus V_minus f_plus f_minus x) :
    ∀ (x y : {x // x ∈ (U : Set (Fin n → ℝ))}),
      EqOn (data x.1 x.2).F (data y.1 y.2).F
        (Metric.ball (fun i => (x.1 i : ℂ)) (data x.1 x.2).r ∩
         Metric.ball (fun i => (y.1 i : ℂ)) (data y.1 y.2).r) := by
  intro x y
  exact localEpsteinData_compat V_plus V_minus hV_plus_open h0 f_plus f_minus
    x.1 y.1 (data x.1 x.2) (data y.1 y.2)

lemma local_eow_epstein_of_data_family
    (V_plus V_minus : Set (Fin n → ℝ))
    (hV_plus_open : IsOpen V_plus)
    (h0 : (0 : Fin n → ℝ) ∈ closure V_plus)
    (f_plus f_minus : (Fin n → ℂ) → ℂ)
    (U : Opens (Fin n → ℝ))
    (data : ∀ x ∈ (U : Set (Fin n → ℝ)), LocalEpsteinData V_plus V_minus f_plus f_minus x) :
    ∃ (W : Opens (Fin n → ℂ)) (F : (Fin n → ℂ) → ℂ),
      (∀ x ∈ U, (fun i => (x i : ℂ)) ∈ W) ∧
      DifferentiableOn ℂ F (W : Set (Fin n → ℂ)) ∧
      EqOn F f_plus ((W : Set (Fin n → ℂ)) ∩ TubeDomain V_plus) ∧
      EqOn F f_minus ((W : Set (Fin n → ℂ)) ∩ TubeDomain V_minus) := by
  have h_compat :=
    localEpsteinData_family_compat V_plus V_minus hV_plus_open h0 f_plus f_minus U data
  exact local_eow_epstein_from_data V_plus V_minus f_plus f_minus U data h_compat

lemma local_eow_epstein_of_core_family
    (V_plus : Set (Fin n → ℝ))
    (hV_plus_open : IsOpen V_plus) (hV_plus_conv : Convex ℝ V_plus)
    (h0 : (0 : Fin n → ℝ) ∈ closure V_plus)
    (f : (Fin n → ℂ) → ℂ)
    (hf_plus_holo : DifferentiableOn ℂ f (TubeDomain V_plus))
    (hf_minus_holo : DifferentiableOn ℂ f (TubeDomain ((fun v : Fin n → ℝ => -v) '' V_plus)))
    (U : Opens (Fin n → ℝ))
    (h_core : ∀ x ∈ (U : Set (Fin n → ℝ)), LocalEOWCore V_plus f x) :
    ∃ (W : Opens (Fin n → ℂ)) (F : (Fin n → ℂ) → ℂ),
      (∀ x ∈ U, (fun i => (x i : ℂ)) ∈ W) ∧
      DifferentiableOn ℂ F (W : Set (Fin n → ℂ)) ∧
      EqOn F f ((W : Set (Fin n → ℂ)) ∩ TubeDomain V_plus) ∧
      EqOn F f ((W : Set (Fin n → ℂ)) ∩ TubeDomain ((fun v : Fin n → ℝ => -v) '' V_plus)) := by
  let data : ∀ x ∈ (U : Set (Fin n → ℝ)),
      LocalEpsteinData V_plus ((fun v : Fin n → ℝ => -v) '' V_plus) f f x :=
    fun x hx => localEpsteinData_of_core V_plus hV_plus_open hV_plus_conv f
      hf_plus_holo hf_minus_holo x (h_core x hx)
  exact local_eow_epstein_of_data_family V_plus ((fun v : Fin n → ℝ => -v) '' V_plus)
    hV_plus_open h0 f f U data

lemma local_eow_epstein_of_local_balls
    (V_plus V_minus : Set (Fin n → ℝ))
    (hV_plus_open : IsOpen V_plus)
    (h0 : (0 : Fin n → ℝ) ∈ closure V_plus)
    (f_plus f_minus : (Fin n → ℂ) → ℂ)
    (U : Opens (Fin n → ℝ))
    (r : (Fin n → ℝ) → ℝ) (hr : ∀ x ∈ (U : Set (Fin n → ℝ)), 0 < r x)
    (F_loc : (Fin n → ℝ) → (Fin n → ℂ) → ℂ)
    (hF_diff : ∀ x ∈ (U : Set (Fin n → ℝ)),
      DifferentiableOn ℂ (F_loc x) (Metric.ball (fun i => (x i : ℂ)) (r x)))
    (hF_plus : ∀ x ∈ (U : Set (Fin n → ℝ)),
      EqOn (F_loc x) f_plus (Metric.ball (fun i => (x i : ℂ)) (r x) ∩ TubeDomain V_plus))
    (hF_minus : ∀ x ∈ (U : Set (Fin n → ℝ)),
      EqOn (F_loc x) f_minus (Metric.ball (fun i => (x i : ℂ)) (r x) ∩ TubeDomain V_minus)) :
    ∃ (W : Opens (Fin n → ℂ)) (F : (Fin n → ℂ) → ℂ),
      (∀ x ∈ U, (fun i => (x i : ℂ)) ∈ W) ∧
      DifferentiableOn ℂ F (W : Set (Fin n → ℂ)) ∧
      EqOn F f_plus ((W : Set (Fin n → ℂ)) ∩ TubeDomain V_plus) ∧
      EqOn F f_minus ((W : Set (Fin n → ℂ)) ∩ TubeDomain V_minus) := by
  let data : ∀ x ∈ (U : Set (Fin n → ℝ)), LocalEpsteinData V_plus V_minus f_plus f_minus x :=
    fun x hx => ⟨r x, hr x hx, F_loc x, hF_diff x hx, hF_plus x hx, hF_minus x hx⟩
  exact local_eow_epstein_of_data_family V_plus V_minus hV_plus_open h0 f_plus f_minus U data

lemma local_epstein_extension_of_data_exists
    (V_plus V_minus : Set (Fin n → ℝ))
    (hV_plus_open : IsOpen V_plus)
    (h0 : (0 : Fin n → ℝ) ∈ closure V_plus)
    (f_plus f_minus : (Fin n → ℂ) → ℂ)
    (U : Opens (Fin n → ℝ))
    (h_data_ex : Nonempty (∀ x ∈ (U : Set (Fin n → ℝ)),
      LocalEpsteinData V_plus V_minus f_plus f_minus x)) :
    ∃ (W : Opens (Fin n → ℂ)) (F : (Fin n → ℂ) → ℂ),
      (∀ x ∈ U, (fun i => (x i : ℂ)) ∈ W) ∧
      DifferentiableOn ℂ F (W : Set (Fin n → ℂ)) ∧
      EqOn F f_plus ((W : Set (Fin n → ℂ)) ∩ TubeDomain V_plus) ∧
      EqOn F f_minus ((W : Set (Fin n → ℂ)) ∩ TubeDomain V_minus) := by
  rcases h_data_ex with ⟨data⟩
  exact local_eow_epstein_of_data_family V_plus V_minus hV_plus_open h0 f_plus f_minus U data

def localEpsteinData_of_entire
    (V_plus V_minus : Set (Fin n → ℝ))
    (G : (Fin n → ℂ) → ℂ) (hG : Differentiable ℂ G)
    (x : Fin n → ℝ) (ρ : ℝ) (hρ : 0 < ρ) :
    LocalEpsteinData V_plus V_minus G G x :=
  ⟨ρ, hρ, G, hG.differentiableOn, fun _ _ => rfl, fun _ _ => rfl⟩

theorem local_eow_epstein_of_entire
    (V_plus V_minus : Set (Fin n → ℝ))
    (hV_plus_open : IsOpen V_plus)
    (h0 : (0 : Fin n → ℝ) ∈ closure V_plus)
    (G : (Fin n → ℂ) → ℂ) (hG : Differentiable ℂ G)
    (U : Opens (Fin n → ℝ)) :
    ∃ (W : Opens (Fin n → ℂ)) (F : (Fin n → ℂ) → ℂ),
      (∀ x ∈ U, (fun i => (x i : ℂ)) ∈ W) ∧
      DifferentiableOn ℂ F (W : Set (Fin n → ℂ)) ∧
      EqOn F G ((W : Set (Fin n → ℂ)) ∩ TubeDomain V_plus) ∧
      EqOn F G ((W : Set (Fin n → ℂ)) ∩ TubeDomain V_minus) := by
  let data : ∀ x ∈ (U : Set (Fin n → ℝ)), LocalEpsteinData V_plus V_minus G G x :=
    fun x _hx => localEpsteinData_of_entire V_plus V_minus G hG x 1 Real.zero_lt_one
  exact local_eow_epstein_of_data_family V_plus V_minus hV_plus_open h0 G G U data

theorem local_eow_epstein_core_all_dims
    (V_plus : Set (Fin n → ℝ))
    (hV_plus_open : IsOpen V_plus) (hV_plus_conv : Convex ℝ V_plus)
    (h0 : (0 : Fin n → ℝ) ∈ closure V_plus)
    (f : (Fin n → ℂ) → ℂ)
    (hf_plus_holo : DifferentiableOn ℂ f (TubeDomain V_plus))
    (hf_minus_holo : DifferentiableOn ℂ f (TubeDomain ((fun v : Fin n → ℝ => -v) '' V_plus)))
    (U : Opens (Fin n → ℝ))
    (h_core : ∀ x ∈ (U : Set (Fin n → ℝ)), LocalEOWCore V_plus f x) :
    ∃ (W : Opens (Fin n → ℂ)) (F : (Fin n → ℂ) → ℂ),
      (∀ x ∈ U, (fun i => (x i : ℂ)) ∈ W) ∧
      DifferentiableOn ℂ F (W : Set (Fin n → ℂ)) ∧
      EqOn F f ((W : Set (Fin n → ℂ)) ∩ TubeDomain V_plus) ∧
      EqOn F f ((W : Set (Fin n → ℂ)) ∩ TubeDomain ((fun v : Fin n → ℝ => -v) '' V_plus)) :=
  local_eow_epstein_of_core_family V_plus hV_plus_open hV_plus_conv h0 f
    hf_plus_holo hf_minus_holo U h_core

theorem local_epstein_data_exists
    (V_plus V_minus : Set (Fin n → ℝ))
    (_h_opposite : V_minus = (fun y => -y) '' V_plus)
    (hV_plus_open : IsOpen V_plus)
    (f_plus : (Fin n → ℂ) → ℂ)
    (f_minus : (Fin n → ℂ) → ℂ)
    (_hf_plus_holo : DifferentiableOn ℂ f_plus (TubeDomain V_plus))
    (_hf_minus_holo : DifferentiableOn ℂ f_minus (TubeDomain V_minus))
    (_T_plus : 𝓓'(Ω_n, ℂ)) (_hT_plus : HasBoundaryValue Ω_n f_plus V_plus _T_plus)
    (_T_minus : 𝓓'(Ω_n, ℂ)) (_hT_minus : HasBoundaryValue Ω_n f_minus V_minus _T_minus)
    (U : Opens (Fin n → ℝ)) (_hU : (U : Set (Fin n → ℝ)) ⊆ Ω_n)
    (_h_match : EqualOn Ω_n _T_plus _T_minus U _hU)
    (_hn : n ≠ 0) (_h_tube : TubeDomain V_plus ≠ ∅) (h0 : (0 : Fin n → ℝ) ∈ closure V_plus)
    (data : ∀ x ∈ (U : Set (Fin n → ℝ)), LocalEpsteinData V_plus V_minus f_plus f_minus x) :
    ∃ (data' : ∀ x ∈ (U : Set (Fin n → ℝ)), LocalEpsteinData V_plus V_minus f_plus f_minus x),
      ∀ (x y : {x // x ∈ (U : Set (Fin n → ℝ))}),
        EqOn (data' x.1 x.2).F (data' y.1 y.2).F
          (Metric.ball (fun i => (x.1 i : ℂ)) (data' x.1 x.2).r ∩
           Metric.ball (fun i => (y.1 i : ℂ)) (data' y.1 y.2).r) :=
  ⟨data, localEpsteinData_family_compat V_plus V_minus hV_plus_open h0 f_plus f_minus U data⟩

lemma local_epstein_extension_exists
    (V_plus V_minus : Set (Fin n → ℝ))
    (h_opposite : V_minus = (fun y => -y) '' V_plus)
    (hV_plus_open : IsOpen V_plus)
    (f_plus : (Fin n → ℂ) → ℂ)
    (f_minus : (Fin n → ℂ) → ℂ)
    (hf_plus_holo : DifferentiableOn ℂ f_plus (TubeDomain V_plus))
    (hf_minus_holo : DifferentiableOn ℂ f_minus (TubeDomain V_minus))
    (T_plus : 𝓓'(Ω_n, ℂ)) (hT_plus : HasBoundaryValue Ω_n f_plus V_plus T_plus)
    (T_minus : 𝓓'(Ω_n, ℂ)) (hT_minus : HasBoundaryValue Ω_n f_minus V_minus T_minus)
    (U : Opens (Fin n → ℝ)) (hU : (U : Set (Fin n → ℝ)) ⊆ Ω_n)
    (h_match : EqualOn Ω_n T_plus T_minus U hU)
    (hn : n ≠ 0) (h_tube : TubeDomain V_plus ≠ ∅) (h0 : (0 : Fin n → ℝ) ∈ closure V_plus)
    (data : ∀ x ∈ (U : Set (Fin n → ℝ)), LocalEpsteinData V_plus V_minus f_plus f_minus x) :
    ∃ (W : Opens (Fin n → ℂ)) (F : (Fin n → ℂ) → ℂ),
      (∀ x ∈ U, (fun i => (x i : ℂ)) ∈ W) ∧
      DifferentiableOn ℂ F (W : Set (Fin n → ℂ)) ∧
      EqOn F f_plus ((W : Set (Fin n → ℂ)) ∩ TubeDomain V_plus) ∧
      EqOn F f_minus ((W : Set (Fin n → ℂ)) ∩ TubeDomain V_minus) := by
  obtain ⟨data', h_compat⟩ := local_epstein_data_exists Ω_n V_plus V_minus h_opposite hV_plus_open
    f_plus f_minus hf_plus_holo hf_minus_holo T_plus hT_plus T_minus hT_minus U hU h_match
    hn h_tube h0 data
  exact local_eow_epstein_from_data V_plus V_minus f_plus f_minus U data' h_compat

theorem local_eow_epstein
    (V_plus V_minus : Set (Fin n → ℝ))
    (h_opposite : V_minus = (fun y => -y) '' V_plus)
    (hV_plus_open : IsOpen V_plus)
    (f_plus : (Fin n → ℂ) → ℂ)
    (f_minus : (Fin n → ℂ) → ℂ)
    (hf_plus_holo : DifferentiableOn ℂ f_plus (TubeDomain V_plus))
    (hf_minus_holo : DifferentiableOn ℂ f_minus (TubeDomain V_minus))
    (T_plus : 𝓓'(Ω_n, ℂ)) (hT_plus : HasBoundaryValue Ω_n f_plus V_plus T_plus)
    (T_minus : 𝓓'(Ω_n, ℂ)) (hT_minus : HasBoundaryValue Ω_n f_minus V_minus T_minus)
    (U : Opens (Fin n → ℝ)) (hU : (U : Set (Fin n → ℝ)) ⊆ Ω_n)
    (h_match : EqualOn Ω_n T_plus T_minus U hU)
    (data : ∀ x ∈ (U : Set (Fin n → ℝ)), LocalEpsteinData V_plus V_minus f_plus f_minus x) :
    ∃ (W : Opens (Fin n → ℂ)) (F : (Fin n → ℂ) → ℂ),
      (∀ x ∈ U, (fun i => (x i : ℂ)) ∈ W) ∧
      DifferentiableOn ℂ F (W : Set (Fin n → ℂ)) ∧
      EqOn F f_plus ((W : Set (Fin n → ℂ)) ∩ TubeDomain V_plus) ∧
      EqOn F f_minus ((W : Set (Fin n → ℂ)) ∩ TubeDomain V_minus) := by
  by_cases hU_empty : (U : Set (Fin n → ℝ)) = ∅
  · exact local_eow_epstein_empty V_plus V_minus f_plus f_minus U hU_empty
  · by_cases h_tube_empty : TubeDomain V_plus = ∅
    · exact local_eow_epstein_empty_tube V_plus V_minus h_opposite f_plus f_minus U h_tube_empty
    · by_cases hn : n = 0
      · exact local_eow_epstein_zero Ω_n V_plus V_minus h_opposite f_plus f_minus
          hf_plus_holo hf_minus_holo T_plus hT_plus T_minus hT_minus U hU h_match hn
      · by_cases h0 : (0 : Fin n → ℝ) ∉ closure V_plus
        · exact local_eow_epstein_case_not_in_closure V_plus V_minus h_opposite f_plus f_minus U h0
        · exact local_epstein_extension_exists Ω_n V_plus V_minus h_opposite hV_plus_open
            f_plus f_minus hf_plus_holo hf_minus_holo T_plus hT_plus T_minus hT_minus U hU h_match
            hn h_tube_empty (not_not.1 h0) data

end Distribution
