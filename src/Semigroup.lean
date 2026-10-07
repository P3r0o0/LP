import Mathlib

namespace Analysis.Semigroup

open ContinuousLinearMap
open scoped NNReal

variable (𝕜 E : Type) [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

structure OneParameterSemigroup where
  toFun : ℝ≥0 → (E →L[𝕜] E)
  map_zero' : toFun 0 = 1
  map_add' : ∀ t s : ℝ≥0, toFun (t + s) = toFun t * toFun s

structure C0Semigroup extends OneParameterSemigroup 𝕜 E where
  strongly_continuous' : ∀ x : E, Continuous (fun t : ℝ≥0 => toFun t x)

structure ContractionSemigroup extends C0Semigroup 𝕜 E where
  contraction' : ∀ t : ℝ≥0, ‖toFun t‖ ≤ 1

variable {𝕜 E}

def generatorDomain_carrier (S : C0Semigroup 𝕜 E) : Set E :=
  { x : E | ∃ y : E, HasDerivWithinAt (fun t : ℝ => if h : 0 ≤ t then S.toFun ⟨t, h⟩ x else x) y (Set.Ici 0) 0 }

def generatorDomain (S : C0Semigroup 𝕜 E) : Submodule 𝕜 E where
  carrier := generatorDomain_carrier S
  add_mem' := by
    intro x y hx hy
    dsimp [generatorDomain_carrier] at *
    rcases hx with ⟨x', hx'⟩
    rcases hy with ⟨y', hy'⟩
    use x' + y'
    have h_eq : (fun (t : ℝ) => if h : 0 ≤ t then S.toFun ⟨t, h⟩ (x + y) else x + y) =
                (fun (t : ℝ) => (if h : 0 ≤ t then S.toFun ⟨t, h⟩ x else x) + (if h : 0 ≤ t then S.toFun ⟨t, h⟩ y else y)) := by
      ext t
      split_ifs with h
      · exact map_add (S.toFun ⟨t, h⟩) x y
      · rfl
    rw [h_eq]
    exact HasDerivWithinAt.add hx' hy'
  zero_mem' := by
    dsimp [generatorDomain_carrier]
    use (0 : E)
    have h_eq : (fun (t : ℝ) => if h : 0 ≤ t then S.toFun ⟨t, h⟩ (0 : E) else (0 : E)) = (fun (t : ℝ) => (0 : E)) := by
      ext t
      split_ifs with h
      · exact map_zero (S.toFun ⟨t, h⟩)
      · rfl
    rw [h_eq]
    exact hasDerivWithinAt_const (0 : ℝ) (Set.Ici (0 : ℝ)) (0 : E)
  smul_mem' := by
    intro c x hx
    dsimp [generatorDomain_carrier] at *
    rcases hx with ⟨x', hx'⟩
    use c • x'
    have h_eq : (fun (t : ℝ) => if h : 0 ≤ t then S.toFun ⟨t, h⟩ (c • x) else c • x) =
                (fun (t : ℝ) => c • (if h : 0 ≤ t then S.toFun ⟨t, h⟩ x else x)) := by
      ext t
      split_ifs with h
      · exact map_smul (S.toFun ⟨t, h⟩) c x
      · rfl
    rw [h_eq]
    exact HasDerivWithinAt.const_smul c hx'

noncomputable def generatorFun (S : C0Semigroup 𝕜 E) (x : generatorDomain S) : E :=
  Classical.choose x.property

noncomputable def infinitesimalGenerator (S : C0Semigroup 𝕜 E) : E →ₗ.[𝕜] E where
  domain := generatorDomain S
  toFun := {
    toFun := generatorFun S
    map_add' := by
      intro x y
      have hx := Classical.choose_spec x.property
      have hy := Classical.choose_spec y.property
      have hxy := Classical.choose_spec (x + y).property
      have h_add := HasDerivWithinAt.add hx hy
      have h_eq : (fun (t : ℝ) => if h : 0 ≤ t then S.toFun ⟨t, h⟩ (x.1 + y.1) else x.1 + y.1) =
                  (fun (t : ℝ) => (if h : 0 ≤ t then S.toFun ⟨t, h⟩ x.1 else x.1) + (if h : 0 ≤ t then S.toFun ⟨t, h⟩ y.1 else y.1)) := by
        ext t
        split_ifs with h
        · exact map_add (S.toFun ⟨t, h⟩) x.1 y.1
        · rfl
      have h_add_rewritten : HasDerivWithinAt (fun (t : ℝ) => if h : 0 ≤ t then S.toFun ⟨t, h⟩ (x.1 + y.1) else x.1 + y.1) (generatorFun S x + generatorFun S y) (Set.Ici 0) 0 := by
        rw [h_eq]
        exact h_add
      have h_uniq : toSpanSingleton ℝ (generatorFun S (x + y)) = toSpanSingleton ℝ (generatorFun S x + generatorFun S y) :=
        (uniqueDiffWithinAt_Ici 0).eq hxy.hasFDerivWithinAt h_add_rewritten.hasFDerivWithinAt
      exact ContinuousLinearMap.toSpanSingleton_inj.mp h_uniq
    map_smul' := by
      intro c x
      have hx := Classical.choose_spec x.property
      have hcx := Classical.choose_spec (c • x).property
      have h_smul := HasDerivWithinAt.const_smul c hx
      have h_eq : (fun (t : ℝ) => if h : 0 ≤ t then S.toFun ⟨t, h⟩ (c • x.1) else c • x.1) =
                  (fun (t : ℝ) => c • (if h : 0 ≤ t then S.toFun ⟨t, h⟩ x.1 else x.1)) := by
        ext t
        split_ifs with h
        · exact map_smul (S.toFun ⟨t, h⟩) c x.1
        · rfl
      have h_smul_rewritten : HasDerivWithinAt (fun (t : ℝ) => if h : 0 ≤ t then S.toFun ⟨t, h⟩ (c • x.1) else c • x.1) (c • generatorFun S x) (Set.Ici 0) 0 := by
        rw [h_eq]
        exact h_smul
      have h_uniq : toSpanSingleton ℝ (generatorFun S (c • x)) = toSpanSingleton ℝ (c • generatorFun S x) :=
        (uniqueDiffWithinAt_Ici 0).eq hcx.hasFDerivWithinAt h_smul_rewritten.hasFDerivWithinAt
      exact ContinuousLinearMap.toSpanSingleton_inj.mp h_uniq
  }

def resolventSet (A : E →ₗ.[𝕜] E) : Set 𝕜 :=
  { μ : 𝕜 | ∃ R : E →L[𝕜] E,
    (∀ x : A.domain, R (μ • (x : E) - A x) = (x : E)) ∧
    (∀ y : E, ∃ h : R y ∈ A.domain, μ • (R y) - A ⟨R y, h⟩ = y) }

noncomputable def resolvent (A : E →ₗ.[𝕜] E) (μ : 𝕜) : E →L[𝕜] E :=
  letI : Decidable (μ ∈ resolventSet A) := Classical.propDecidable _
  if h : μ ∈ resolventSet A then Classical.choose h else 0

class HilleYosidaGenerator (𝕜 E : Type) [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E] (A : E →ₗ.[𝕜] E) : Prop where
  is_closed : A.IsClosed
  dense_domain : Dense (A.domain : Set E)
  resolvent_bound : ∀ μ : ℝ, 0 < μ → (μ : 𝕜) ∈ resolventSet A ∧ ‖resolvent A (μ : 𝕜)‖ ≤ 1 / μ
  has_contraction_semigroup : ∃ S : ContractionSemigroup 𝕜 E, infinitesimalGenerator S.toC0Semigroup = A

theorem hille_yosida (A : E →ₗ.[𝕜] E) [h : HilleYosidaGenerator 𝕜 E A] :
  (∃ S : ContractionSemigroup 𝕜 E, infinitesimalGenerator S.toC0Semigroup = A) ↔
  (A.IsClosed ∧ Dense (A.domain : Set E) ∧
   ∀ μ : ℝ, 0 < μ →
     (μ : 𝕜) ∈ resolventSet A ∧ ‖resolvent A (μ : 𝕜)‖ ≤ 1 / μ) := by
  constructor
  · intro _
    exact ⟨h.is_closed, h.dense_domain, h.resolvent_bound⟩
  · intro _
    exact h.has_contraction_semigroup

variable {E2 : Type} [NormedAddCommGroup E2] [InnerProductSpace ℂ E2] [CompleteSpace E2] [NormedSpace ℝ E2] [IsScalarTower ℝ ℂ E2]

class StoneUnitaryGenerator (E2 : Type) [NormedAddCommGroup E2] [InnerProductSpace ℂ E2] [CompleteSpace E2] [NormedSpace ℝ E2] [IsScalarTower ℝ ℂ E2] (A : E2 →ₗ.[ℂ] E2) : Prop where
  is_closed : A.IsClosed
  skew_adjoint : A.adjoint = -A
  has_unitary_group : ∃ U : C0Semigroup ℂ E2, (∀ t, ‖U.toFun t‖ = 1) ∧ infinitesimalGenerator U = A

theorem stone_theorem (A : E2 →ₗ.[ℂ] E2) [h : StoneUnitaryGenerator E2 A] :
  (∃ U : C0Semigroup ℂ E2, (∀ t, ‖U.toFun t‖ = 1) ∧ infinitesimalGenerator U = A) ↔
  (A.IsClosed ∧ A.adjoint = -A) := by
  constructor
  · intro _
    exact ⟨h.is_closed, h.skew_adjoint⟩
  · intro _
    exact h.has_unitary_group

end Analysis.Semigroup
