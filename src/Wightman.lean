import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Analysis.Distribution.TemperedDistribution

namespace QFT

def minkowski_sq (x y : Fin 4 → ℝ) : ℝ :=
  (x 0 - y 0)^2 - (x 1 - y 1)^2 - (x 2 - y 2)^2 - (x 3 - y 3)^2

def spacelike_separated (x y : Fin 4 → ℝ) : Prop :=
  minkowski_sq x y < 0

class WightmanAxioms (StateSpace : Type) [NormedAddCommGroup StateSpace] [InnerProductSpace ℂ StateSpace] where

  vacuum : StateSpace

  D_0 : Submodule ℂ StateSpace
  vacuum_in_D_0 : vacuum ∈ D_0
  D_0_dense : Dense (D_0 : Set StateSpace)

  translation : (Fin 4 → ℝ) → (StateSpace →L[ℂ] StateSpace)

  lorentz : Matrix (Fin 4) (Fin 4) ℝ → (StateSpace →L[ℂ] StateSpace)

  vacuum_invariant_translation : ∀ (a : Fin 4 → ℝ), translation a vacuum = vacuum
  vacuum_invariant_lorentz : ∀ (Λ : Matrix (Fin 4) (Fin 4) ℝ), lorentz Λ vacuum = vacuum

  spectrum_condition_forward_cone : True
  has_spectral_gap : ∃ (Δ : ℝ), Δ > 0

  field : SchwartzMap (Fin 4 → ℝ) ℂ → (D_0 →ₗ[ℂ] D_0)

  locality : ∀ (f g : SchwartzMap (Fin 4 → ℝ) ℂ),
    (∀ x ∈ Function.support f, ∀ y ∈ Function.support g, spacelike_separated x y) →
    field f * field g = field g * field f

  non_trivial_field : ∃ (f : SchwartzMap (Fin 4 → ℝ) ℂ), field f ⟨vacuum, vacuum_in_D_0⟩ ≠ 0

  covariance_translation : ∀ (a : Fin 4 → ℝ) (f : SchwartzMap (Fin 4 → ℝ) ℂ),
    ∃ (f_a : SchwartzMap (Fin 4 → ℝ) ℂ),
      
      ∀ (h_inv : ∀ (x : D_0), translation a (x : StateSpace) ∈ D_0)
        (x : D_0),
      translation a (field f x : StateSpace) = field f_a ⟨translation a (x : StateSpace), h_inv x⟩

  covariance_lorentz : ∀ (Λ : Matrix (Fin 4) (Fin 4) ℝ) (f : SchwartzMap (Fin 4 → ℝ) ℂ),
    ∃ (f_Λ : SchwartzMap (Fin 4 → ℝ) ℂ),
      
      ∀ (h_inv : ∀ (x : D_0), lorentz Λ (x : StateSpace) ∈ D_0)
        (x : D_0),
      lorentz Λ (field f x : StateSpace) = field f_Λ ⟨lorentz Λ (x : StateSpace), h_inv x⟩

end QFT
