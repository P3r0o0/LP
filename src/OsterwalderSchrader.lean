import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Data.Matrix.Basic
import Semigroup

open scoped InnerProductSpace
open scoped NNReal
open Complex

namespace QFT

class OsterwalderSchrader (StateSpace : Type) [NormedAddCommGroup StateSpace] [InnerProductSpace ℂ StateSpace] where

  Observable : Type
  obsRing : Ring Observable
  obsAlgebra : Algebra ℂ Observable

  act : Observable → StateSpace → StateSpace

  vacuum : StateSpace
  vacuum_norm : ‖vacuum‖ = 1

  timeReversal : Observable → Observable

  reflection_positivity : ∀ (A : Observable),
    0 ≤ (⟪act (timeReversal A) vacuum, act A vacuum⟫_ℂ).re

  timeEvolution : Analysis.Semigroup.C0Semigroup ℂ StateSpace

  has_spectral_gap : ∃ (Δ : ℝ), Δ > 0 ∧
    ∀ (Ψ : StateSpace), ⟪vacuum, Ψ⟫_ℂ = 0 →
      ∀ (t : NNReal), t > 0 →
        (⟪Ψ, timeEvolution.toFun t Ψ⟫_ℂ).re ≤ Real.exp (-Δ * (t : ℝ)) * (⟪Ψ, Ψ⟫_ℂ).re

  spaceTranslation : (Fin 3 → ℝ) → StateSpace → StateSpace

  spaceRotation : Matrix (Fin 3) (Fin 3) ℝ → StateSpace → StateSpace

  euclideanRotation : Matrix (Fin 4) (Fin 4) ℝ → StateSpace → StateSpace

  euclidean_invariance :
    (∀ (v : Fin 3 → ℝ), spaceTranslation v vacuum = vacuum) ∧
    (∀ (t : NNReal), timeEvolution.toFun t vacuum = vacuum) ∧
    (∀ (R : Matrix (Fin 3) (Fin 3) ℝ), spaceRotation R vacuum = vacuum) ∧
    (∀ (R : Matrix (Fin 4) (Fin 4) ℝ), euclideanRotation R vacuum = vacuum)

  non_trivial : ∃ (Ψ : StateSpace), ⟪vacuum, Ψ⟫_ℂ = 0 ∧ Ψ ≠ 0

  cluster_property :
    ∀ (A B : Observable),
      Filter.Tendsto (fun (v : Fin 3 → ℝ) => (⟪act A vacuum, spaceTranslation v (act B vacuum)⟫_ℂ).re)
      (Filter.cocompact (Fin 3 → ℝ)) (nhds ((⟪act A vacuum, vacuum⟫_ℂ).re * (⟪vacuum, act B vacuum⟫_ℂ).re))

end QFT
