import VectorBHW
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Topology.Algebra.LinearMapCompletion

namespace QFT

open Geometry Geometry.PolarDecomposition MeasureTheory Filter Topology Matrix
open scoped ComplexOrder FourierTransform RealInnerProductSpace Interval ContDiff InnerProductSpace

def euclidInner (x y : Fin 4 → ℝ) : ℝ :=
  ∑ μ : Fin 4, x μ * y μ

lemma euclidInner_explicit (x y : Fin 4 → ℝ) :
    euclidInner x y = x 0 * y 0 + x 1 * y 1 + x 2 * y 2 + x 3 * y 3 := by
  simp [euclidInner, Fin.sum_univ_four]

lemma euclidInner_comm (x y : Fin 4 → ℝ) :
    euclidInner x y = euclidInner y x := by
  rw [euclidInner_explicit, euclidInner_explicit]
  ring

lemma euclidInner_add_left (x y z : Fin 4 → ℝ) :
    euclidInner (x + y) z = euclidInner x z + euclidInner y z := by
  simp only [euclidInner_explicit, Pi.add_apply]
  ring

lemma euclidInner_add_right (x y z : Fin 4 → ℝ) :
    euclidInner x (y + z) = euclidInner x y + euclidInner x z := by
  simp only [euclidInner_explicit, Pi.add_apply]
  ring

lemma euclidInner_smul_left (c : ℝ) (x y : Fin 4 → ℝ) :
    euclidInner (c • x) y = c * euclidInner x y := by
  simp only [euclidInner_explicit, Pi.smul_apply, smul_eq_mul]
  ring

lemma euclidInner_smul_right (c : ℝ) (x y : Fin 4 → ℝ) :
    euclidInner x (c • y) = c * euclidInner x y := by
  simp only [euclidInner_explicit, Pi.smul_apply, smul_eq_mul]
  ring

@[simp]
lemma euclidInner_neg_left (x y : Fin 4 → ℝ) :
    euclidInner (-x) y = -euclidInner x y := by
  simp only [euclidInner_explicit, Pi.neg_apply]
  ring

@[simp]
lemma euclidInner_neg_right (x y : Fin 4 → ℝ) :
    euclidInner x (-y) = -euclidInner x y := by
  simp only [euclidInner_explicit, Pi.neg_apply]
  ring

@[simp]
lemma euclidInner_zero_left (y : Fin 4 → ℝ) :
    euclidInner 0 y = 0 := by
  simp [euclidInner_explicit]

@[simp]
lemma euclidInner_zero_right (x : Fin 4 → ℝ) :
    euclidInner x 0 = 0 := by
  simp [euclidInner_explicit]

lemma euclidInner_self_nonneg (x : Fin 4 → ℝ) :
    0 ≤ euclidInner x x := by
  rw [euclidInner_explicit]
  nlinarith [mul_self_nonneg (x 0), mul_self_nonneg (x 1),
    mul_self_nonneg (x 2), mul_self_nonneg (x 3)]

lemma euclidInner_self_eq_zero_iff (x : Fin 4 → ℝ) :
    euclidInner x x = 0 ↔ x = 0 := by
  constructor
  · intro h
    rw [euclidInner_explicit] at h
    have s0 := mul_self_nonneg (x 0)
    have s1 := mul_self_nonneg (x 1)
    have s2 := mul_self_nonneg (x 2)
    have s3 := mul_self_nonneg (x 3)
    have h0 : x 0 = 0 := mul_self_eq_zero.mp (by linarith)
    have h1 : x 1 = 0 := mul_self_eq_zero.mp (by linarith)
    have h2 : x 2 = 0 := mul_self_eq_zero.mp (by linarith)
    have h3 : x 3 = 0 := mul_self_eq_zero.mp (by linarith)
    ext μ
    fin_cases μ
    · exact h0
    · exact h1
    · exact h2
    · exact h3
  · rintro rfl
    exact euclidInner_zero_left 0

def euclidTimeReflect (x : Fin 4 → ℝ) : Fin 4 → ℝ :=
  fun μ => if μ = 0 then -x 0 else x μ

@[simp]
lemma euclidTimeReflect_zero_coord (x : Fin 4 → ℝ) :
    euclidTimeReflect x 0 = -x 0 := rfl

lemma euclidTimeReflect_of_ne_zero (x : Fin 4 → ℝ) {μ : Fin 4} (hμ : μ ≠ 0) :
    euclidTimeReflect x μ = x μ := by
  dsimp [euclidTimeReflect]
  rw [if_neg hμ]

@[simp]
lemma euclidTimeReflect_involutive (x : Fin 4 → ℝ) :
    euclidTimeReflect (euclidTimeReflect x) = x := by
  ext μ
  fin_cases μ <;> simp [euclidTimeReflect]

@[simp]
lemma euclidTimeReflect_zero :
    euclidTimeReflect 0 = 0 := by
  ext μ
  fin_cases μ <;> simp [euclidTimeReflect]

lemma euclidTimeReflect_add (x y : Fin 4 → ℝ) :
    euclidTimeReflect (x + y) = euclidTimeReflect x + euclidTimeReflect y := by
  ext μ
  fin_cases μ <;> simp [euclidTimeReflect, add_comm]

lemma euclidTimeReflect_sub (x y : Fin 4 → ℝ) :
    euclidTimeReflect (x - y) = euclidTimeReflect x - euclidTimeReflect y := by
  ext μ
  fin_cases μ <;> simp [euclidTimeReflect, sub_eq_add_neg, add_comm]

lemma euclidTimeReflect_neg (x : Fin 4 → ℝ) :
    euclidTimeReflect (-x) = -euclidTimeReflect x := by
  ext μ
  fin_cases μ <;> simp [euclidTimeReflect]

lemma euclidTimeReflect_smul (c : ℝ) (x : Fin 4 → ℝ) :
    euclidTimeReflect (c • x) = c • euclidTimeReflect x := by
  ext μ
  fin_cases μ <;> simp [euclidTimeReflect]

lemma euclidInner_euclidTimeReflect (x y : Fin 4 → ℝ) :
    euclidInner (euclidTimeReflect x) (euclidTimeReflect y) = euclidInner x y := by
  simp only [euclidInner_explicit, euclidTimeReflect, ↓reduceIte, Fin.isValue, Fin.reduceEq]
  ring

def euclidTimeReflectN (n : ℕ) (x : Fin n → Fin 4 → ℝ) : Fin n → Fin 4 → ℝ :=
  fun i => euclidTimeReflect (x i)

def euclidTimeReflectRev (n : ℕ) (x : Fin n → Fin 4 → ℝ) : Fin n → Fin 4 → ℝ :=
  fun i => euclidTimeReflect (x (Fin.rev i))

@[simp]
lemma euclidTimeReflectN_involutive (n : ℕ) (x : Fin n → Fin 4 → ℝ) :
    euclidTimeReflectN n (euclidTimeReflectN n x) = x := by
  ext i μ
  exact congrFun (euclidTimeReflect_involutive (x i)) μ

@[simp]
lemma euclidTimeReflectRev_involutive (n : ℕ) (x : Fin n → Fin 4 → ℝ) :
    euclidTimeReflectRev n (euclidTimeReflectRev n x) = x := by
  ext i μ
  dsimp [euclidTimeReflectRev]
  rw [Fin.rev_rev]
  exact congrFun (euclidTimeReflect_involutive (x i)) μ

def wickEmbed (x : Fin 4 → ℝ) : Fin 4 → ℂ :=
  fun μ => if μ = 0 then (x 0 : ℂ) * Complex.I else (x μ : ℂ)

@[simp]
lemma wickEmbed_zero_coord (x : Fin 4 → ℝ) :
    wickEmbed x 0 = (x 0 : ℂ) * Complex.I := rfl

lemma wickEmbed_of_ne_zero (x : Fin 4 → ℝ) {μ : Fin 4} (hμ : μ ≠ 0) :
    wickEmbed x μ = (x μ : ℂ) := by
  dsimp [wickEmbed]
  rw [if_neg hμ]

@[simp]
lemma wickEmbed_re (x : Fin 4 → ℝ) (μ : Fin 4) :
    (wickEmbed x μ).re = if μ = 0 then 0 else x μ := by
  fin_cases μ <;> simp [wickEmbed]

@[simp]
lemma wickEmbed_im (x : Fin 4 → ℝ) (μ : Fin 4) :
    (wickEmbed x μ).im = if μ = 0 then x 0 else 0 := by
  fin_cases μ <;> simp [wickEmbed]

@[simp]
lemma wickEmbed_zero :
    wickEmbed 0 = 0 := by
  ext μ
  fin_cases μ <;> simp [wickEmbed]

lemma wickEmbed_add (x y : Fin 4 → ℝ) :
    wickEmbed (x + y) = wickEmbed x + wickEmbed y := by
  ext μ
  fin_cases μ <;> simp [wickEmbed, add_mul]

lemma wickEmbed_sub (x y : Fin 4 → ℝ) :
    wickEmbed (x - y) = wickEmbed x - wickEmbed y := by
  ext μ
  fin_cases μ <;> simp [wickEmbed, sub_mul]

lemma wickEmbed_neg (x : Fin 4 → ℝ) :
    wickEmbed (-x) = -wickEmbed x := by
  ext μ
  fin_cases μ <;> simp [wickEmbed]

lemma wickEmbed_smul (c : ℝ) (x : Fin 4 → ℝ) :
    wickEmbed (c • x) = c • wickEmbed x := by
  ext μ
  fin_cases μ <;> simp [wickEmbed, Complex.real_smul, mul_assoc]

lemma wickEmbed_injective : Function.Injective wickEmbed := by
  intro x y h
  ext μ
  fin_cases μ
  · have h0 := congrArg Complex.im (congrFun h 0)
    simpa [wickEmbed] using h0
  · have h1 := congrArg Complex.re (congrFun h 1)
    simpa [wickEmbed] using h1
  · have h2 := congrArg Complex.re (congrFun h 2)
    simpa [wickEmbed] using h2
  · have h3 := congrArg Complex.re (congrFun h 3)
    simpa [wickEmbed] using h3

noncomputable def wickEmbedCLM : (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := wickEmbed
      map_add' := wickEmbed_add
      map_smul' := fun c x => by
        simp only [RingHom.id_apply]
        exact wickEmbed_smul c x }

lemma continuous_wickEmbed : Continuous wickEmbed :=
  wickEmbedCLM.continuous

lemma minkowskiInnerC_wickEmbed (x y : Fin 4 → ℝ) :
    minkowskiInnerC (wickEmbed x) (wickEmbed y) = -(euclidInner x y : ℂ) := by
  dsimp [minkowskiInnerC, wickEmbed]
  rw [euclidInner_explicit]
  push_cast
  have hI2 : Complex.I * Complex.I = -1 := Complex.I_mul_I
  calc
    (x 0 : ℂ) * Complex.I * ((y 0 : ℂ) * Complex.I) -
        (x 1 : ℂ) * (y 1 : ℂ) - (x 2 : ℂ) * (y 2 : ℂ) - (x 3 : ℂ) * (y 3 : ℂ)
      = (x 0 : ℂ) * (y 0 : ℂ) * (Complex.I * Complex.I) -
        (x 1 : ℂ) * (y 1 : ℂ) - (x 2 : ℂ) * (y 2 : ℂ) - (x 3 : ℂ) * (y 3 : ℂ) := by ring
    _ = -((x 0 : ℂ) * (y 0 : ℂ) + (x 1 : ℂ) * (y 1 : ℂ) +
        (x 2 : ℂ) * (y 2 : ℂ) + (x 3 : ℂ) * (y 3 : ℂ)) := by rw [hI2]; ring

lemma star_wickEmbed (x : Fin 4 → ℝ) :
    (fun μ => star (wickEmbed x μ)) = wickEmbed (euclidTimeReflect x) := by
  ext μ
  fin_cases μ <;> simp [wickEmbed, euclidTimeReflect]

lemma conjTranspose_vec_to_spinor_wickEmbed (x : Fin 4 → ℝ) :
    (vec_to_spinor (wickEmbed x))ᴴ = vec_to_spinor (wickEmbed (euclidTimeReflect x)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [vec_to_spinor, wickEmbed, euclidTimeReflect, sigma_0, sigma_1, sigma_2, sigma_3,
      Matrix.conjTranspose_apply]

lemma det_vec_to_spinor_wickEmbed (x : Fin 4 → ℝ) :
    (vec_to_spinor (wickEmbed x)).det = -(euclidInner x x : ℂ) := by
  rw [vec_to_spinor_det]
  have h : (wickEmbed x 0) ^ 2 - (wickEmbed x 1) ^ 2 -
      (wickEmbed x 2) ^ 2 - (wickEmbed x 3) ^ 2 =
      minkowskiInnerC (wickEmbed x) (wickEmbed x) := by
    dsimp [minkowskiInnerC]
    ring
  rw [h, minkowskiInnerC_wickEmbed]

def wickEmbedN (n : ℕ) (x : Fin n → Fin 4 → ℝ) : Fin n → Fin 4 → ℂ :=
  fun i => wickEmbed (x i)

@[simp]
lemma wickEmbedN_apply (n : ℕ) (x : Fin n → Fin 4 → ℝ) (i : Fin n) :
    wickEmbedN n x i = wickEmbed (x i) := rfl

@[simp]
lemma wickEmbedN_zero (n : ℕ) :
    wickEmbedN n 0 = 0 := by
  ext i μ
  exact congrFun wickEmbed_zero μ

lemma wickEmbedN_add (n : ℕ) (x y : Fin n → Fin 4 → ℝ) :
    wickEmbedN n (x + y) = wickEmbedN n x + wickEmbedN n y := by
  ext i μ
  exact congrFun (wickEmbed_add (x i) (y i)) μ

lemma wickEmbedN_sub (n : ℕ) (x y : Fin n → Fin 4 → ℝ) :
    wickEmbedN n (x - y) = wickEmbedN n x - wickEmbedN n y := by
  ext i μ
  exact congrFun (wickEmbed_sub (x i) (y i)) μ

lemma wickEmbedN_neg (n : ℕ) (x : Fin n → Fin 4 → ℝ) :
    wickEmbedN n (-x) = -wickEmbedN n x := by
  ext i μ
  exact congrFun (wickEmbed_neg (x i)) μ

lemma wickEmbedN_smul (n : ℕ) (c : ℝ) (x : Fin n → Fin 4 → ℝ) :
    wickEmbedN n (c • x) = c • wickEmbedN n x := by
  ext i μ
  exact congrFun (wickEmbed_smul c (x i)) μ

lemma wickEmbedN_injective (n : ℕ) : Function.Injective (wickEmbedN n) := by
  intro x y h
  ext i μ
  have hi := congrFun h i
  exact congrFun (wickEmbed_injective hi) μ

noncomputable def wickEmbedNCLM (n : ℕ) :
    (Fin n → Fin 4 → ℝ) →L[ℝ] (Fin n → Fin 4 → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := wickEmbedN n
      map_add' := wickEmbedN_add n
      map_smul' := fun c x => by
        simp only [RingHom.id_apply]
        exact wickEmbedN_smul n c x }

lemma continuous_wickEmbedN (n : ℕ) : Continuous (wickEmbedN n) :=
  (wickEmbedNCLM n).continuous

lemma wickEmbedN_comp_rev (n : ℕ) (x : Fin n → Fin 4 → ℝ) :
    wickEmbedN n (x ∘ Fin.rev) = (wickEmbedN n x) ∘ Fin.rev := rfl

lemma star_wickEmbedN (n : ℕ) (x : Fin n → Fin 4 → ℝ) :
    (fun i μ => star (wickEmbedN n x i μ)) = wickEmbedN n (euclidTimeReflectN n x) := by
  ext i μ
  exact congrFun (star_wickEmbed (x i)) μ

lemma wickEmbedN_euclidTimeReflectRev (n : ℕ) (x : Fin n → Fin 4 → ℝ) :
    wickEmbedN n (euclidTimeReflectRev n x) =
      fun i μ => star (wickEmbedN n x (Fin.rev i) μ) := by
  ext i μ
  exact (congrFun (star_wickEmbed (x (Fin.rev i))) μ).symm

def euclidPosTime : Set (Fin 4 → ℝ) :=
  { x | 0 < x 0 }

def orderedEuclidN (n : ℕ) : Set (Fin n → Fin 4 → ℝ) :=
  { x | ∀ (i : Fin n) (hi : i.val + 1 < n), x i 0 < x ⟨i.val + 1, hi⟩ 0 }

def posOrderedEuclidN (n : ℕ) : Set (Fin n → Fin 4 → ℝ) :=
  { x | (∀ i : Fin n, 0 < x i 0) ∧ x ∈ orderedEuclidN n }

lemma posOrderedEuclidN_subset_orderedEuclidN (n : ℕ) :
    posOrderedEuclidN n ⊆ orderedEuclidN n :=
  fun _ hx => hx.2

lemma isOpen_euclidPosTime : IsOpen euclidPosTime :=
  isOpen_lt continuous_const (continuous_apply 0)

lemma convex_euclidPosTime : Convex ℝ euclidPosTime := by
  intro x hx y hy a b ha hb hab
  change 0 < a * x 0 + b * y 0
  have hx0 : 0 < x 0 := hx
  have hy0 : 0 < y 0 := hy
  by_cases ha0 : a = 0
  · subst ha0
    have hb1 : b = 1 := by linarith
    subst hb1
    linarith
  · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have h1 : 0 < a * x 0 := mul_pos ha_pos hx0
    have h2 : 0 ≤ b * y 0 := mul_nonneg hb (le_of_lt hy0)
    linarith

lemma wickEmbed_sub_neg_im (x y : Fin 4 → ℝ) :
    (fun μ : Fin 4 => -((wickEmbed x - wickEmbed y) μ).im) =
      fun μ : Fin 4 => if μ = 0 then y 0 - x 0 else 0 := by
  ext μ
  fin_cases μ <;> simp [wickEmbed]

lemma wickEmbed_sub_neg_im_mem_forward_light_cone_iff (x y : Fin 4 → ℝ) :
    (fun μ : Fin 4 => -((wickEmbed x - wickEmbed y) μ).im) ∈ forward_light_cone ↔
      x 0 < y 0 := by
  rw [wickEmbed_sub_neg_im]
  dsimp [forward_light_cone]
  rw [minkowskiInner_explicit]
  simp only [ ↓reduceIte, Fin.isValue, Fin.reduceEq, mul_zero, sub_zero]
  constructor
  · rintro ⟨h1, _⟩
    linarith
  · intro h
    have hpos : 0 < y 0 - x 0 := sub_pos.mpr h
    exact ⟨hpos, mul_pos hpos hpos⟩

theorem wickEmbedN_mem_forward_tube_n_iff (n : ℕ) (x : Fin n → Fin 4 → ℝ) :
    wickEmbedN n x ∈ forward_tube_n n ↔ x ∈ orderedEuclidN n := by
  dsimp [forward_tube_n, orderedEuclidN, wickEmbedN]
  constructor
  · intro hx i hi
    exact (wickEmbed_sub_neg_im_mem_forward_light_cone_iff (x i) (x ⟨i.val + 1, hi⟩)).mp (hx i hi)
  · intro hx i hi
    exact (wickEmbed_sub_neg_im_mem_forward_light_cone_iff (x i) (x ⟨i.val + 1, hi⟩)).mpr (hx i hi)

lemma wickEmbedN_mem_forward_tube_n (n : ℕ) {x : Fin n → Fin 4 → ℝ}
    (hx : x ∈ orderedEuclidN n) :
    wickEmbedN n x ∈ forward_tube_n n :=
  (wickEmbedN_mem_forward_tube_n_iff n x).mpr hx

lemma wickEmbedN_mem_extended_tube_n (n : ℕ) {x : Fin n → Fin 4 → ℝ}
    (hx : x ∈ orderedEuclidN n) :
    wickEmbedN n x ∈ extended_tube_n n := by
  dsimp [extended_tube_n]
  rw [Set.mem_iUnion]
  refine ⟨1, wickEmbedN n x, wickEmbedN_mem_forward_tube_n n hx, ?_⟩
  exact one_smul _ _

lemma isOpen_orderedEuclidN (n : ℕ) : IsOpen (orderedEuclidN n) := by
  have h_eq : orderedEuclidN n = (wickEmbedN n) ⁻¹' (forward_tube_n n) := by
    ext x
    exact (wickEmbedN_mem_forward_tube_n_iff n x).symm
  rw [h_eq]
  exact (forward_tube_n_isOpen n).preimage (continuous_wickEmbedN n)

lemma convex_orderedEuclidN (n : ℕ) : Convex ℝ (orderedEuclidN n) := by
  intro x hx y hy a b ha hb hab i hi
  change a * x i 0 + b * y i 0 < a * x ⟨i.val + 1, hi⟩ 0 + b * y ⟨i.val + 1, hi⟩ 0
  have hxi : x i 0 < x ⟨i.val + 1, hi⟩ 0 := hx i hi
  have hyi : y i 0 < y ⟨i.val + 1, hi⟩ 0 := hy i hi
  by_cases ha0 : a = 0
  · subst ha0
    have hb1 : b = 1 := by linarith
    subst hb1
    linarith
  · have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    have h1 : a * x i 0 < a * x ⟨i.val + 1, hi⟩ 0 := mul_lt_mul_of_pos_left hxi ha_pos
    have h2 : b * y i 0 ≤ b * y ⟨i.val + 1, hi⟩ 0 := mul_le_mul_of_nonneg_left (le_of_lt hyi) hb
    linarith

lemma isOpen_posOrderedEuclidN (n : ℕ) : IsOpen (posOrderedEuclidN n) := by
  have h_pos : IsOpen {x : Fin n → Fin 4 → ℝ | ∀ i : Fin n, 0 < x i 0} := by
    rw [Set.setOf_forall]
    exact isOpen_iInter_of_finite (fun i =>
      isOpen_lt continuous_const ((continuous_apply 0).comp (continuous_apply i)))
  exact h_pos.inter (isOpen_orderedEuclidN n)

lemma convex_posOrderedEuclidN (n : ℕ) : Convex ℝ (posOrderedEuclidN n) := by
  intro x hx y hy a b ha hb hab
  refine ⟨fun i => ?_, convex_orderedEuclidN n hx.2 hy.2 ha hb hab⟩
  exact convex_euclidPosTime (hx.1 i) (hy.1 i) ha hb hab

def euclidOrderedBasePoint (n : ℕ) : Fin n → Fin 4 → ℝ :=
  fun i μ => if μ = 0 then (i.val : ℝ) + 1 else 0

lemma euclidOrderedBasePoint_mem_posOrderedEuclidN (n : ℕ) :
    euclidOrderedBasePoint n ∈ posOrderedEuclidN n := by
  refine ⟨fun i => ?_, fun i hi => ?_⟩
  · dsimp [euclidOrderedBasePoint]
    positivity
  · dsimp [euclidOrderedBasePoint]
    have hlt : (i.val : ℝ) < ((i.val + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.lt_succ_self i.val
    linarith

lemma euclidOrderedBasePoint_mem_orderedEuclidN (n : ℕ) :
    euclidOrderedBasePoint n ∈ orderedEuclidN n :=
  (euclidOrderedBasePoint_mem_posOrderedEuclidN n).2

lemma orderedEuclidN_nonempty (n : ℕ) : (orderedEuclidN n).Nonempty :=
  ⟨euclidOrderedBasePoint n, euclidOrderedBasePoint_mem_orderedEuclidN n⟩

lemma posOrderedEuclidN_nonempty (n : ℕ) : (posOrderedEuclidN n).Nonempty :=
  ⟨euclidOrderedBasePoint n, euclidOrderedBasePoint_mem_posOrderedEuclidN n⟩

lemma shift_mem_orderedEuclidN (n : ℕ) {x : Fin n → Fin 4 → ℝ}
    (hx : x ∈ orderedEuclidN n) (a : Fin 4 → ℝ) :
    (fun i => x i + a) ∈ orderedEuclidN n := by
  intro i hi
  simp only [Pi.add_apply]
  linarith [hx i hi]

lemma neg_rev_mem_orderedEuclidN (n : ℕ) {x : Fin n → Fin 4 → ℝ}
    (hx : x ∈ orderedEuclidN n) :
    (-(x ∘ Fin.rev)) ∈ orderedEuclidN n := by
  rw [← wickEmbedN_mem_forward_tube_n_iff]
  rw [wickEmbedN_neg, wickEmbedN_comp_rev]
  exact neg_rev_mem_forward_tube_n n (wickEmbedN n x) (wickEmbedN_mem_forward_tube_n n hx)

lemma neg_rev_mem_orderedEuclidN_iff (n : ℕ) (x : Fin n → Fin 4 → ℝ) :
    (-(x ∘ Fin.rev)) ∈ orderedEuclidN n ↔ x ∈ orderedEuclidN n := by
  constructor
  · intro h
    have h' := neg_rev_mem_orderedEuclidN n h
    have h_inv : -((-(x ∘ Fin.rev)) ∘ Fin.rev) = x := by
      ext i μ
      simp [Fin.rev_rev]
    rwa [h_inv] at h'
  · exact neg_rev_mem_orderedEuclidN n

lemma euclidTimeReflectRev_mem_orderedEuclidN (n : ℕ) {x : Fin n → Fin 4 → ℝ}
    (hx : x ∈ orderedEuclidN n) :
    euclidTimeReflectRev n x ∈ orderedEuclidN n := by
  intro i hi
  dsimp [euclidTimeReflectRev, euclidTimeReflect]
  have h_neg : (-(x ∘ Fin.rev)) i 0 < (-(x ∘ Fin.rev)) ⟨i.val + 1, hi⟩ 0 :=
    neg_rev_mem_orderedEuclidN n hx i hi
  simpa using h_neg

lemma euclidTimeReflectRev_mem_orderedEuclidN_iff (n : ℕ) (x : Fin n → Fin 4 → ℝ) :
    euclidTimeReflectRev n x ∈ orderedEuclidN n ↔ x ∈ orderedEuclidN n := by
  constructor
  · intro h
    have h' := euclidTimeReflectRev_mem_orderedEuclidN n h
    rwa [euclidTimeReflectRev_involutive] at h'
  · exact euclidTimeReflectRev_mem_orderedEuclidN n

lemma wickEmbedN_euclidTimeReflectN_mem_backward_tube_n (n : ℕ)
    {x : Fin n → Fin 4 → ℝ} (hx : x ∈ orderedEuclidN n) :
    wickEmbedN n (euclidTimeReflectN n x) ∈ backward_tube_n n := by
  have h_rev : euclidTimeReflectRev n x ∈ orderedEuclidN n :=
    euclidTimeReflectRev_mem_orderedEuclidN n hx
  have h_fwd : wickEmbedN n (euclidTimeReflectRev n x) ∈ forward_tube_n n :=
    wickEmbedN_mem_forward_tube_n n h_rev
  have h_bwd := rev_mem_backward_tube_n n (wickEmbedN n (euclidTimeReflectRev n x)) h_fwd
  have h_eq : (wickEmbedN n (euclidTimeReflectRev n x)) ∘ Fin.rev =
      wickEmbedN n (euclidTimeReflectN n x) := by
    ext i μ
    dsimp [wickEmbedN, euclidTimeReflectRev, euclidTimeReflectN]
    rw [Fin.rev_rev]
  rwa [h_eq] at h_bwd

lemma wickEmbedN_euclidTimeReflectN_mem_extended_tube_n (n : ℕ)
    {x : Fin n → Fin 4 → ℝ} (hx : x ∈ orderedEuclidN n) :
    wickEmbedN n (euclidTimeReflectN n x) ∈ extended_tube_n n :=
  backward_tube_subset_extended_tube_n n
    (wickEmbedN_euclidTimeReflectN_mem_backward_tube_n n hx)

lemma wickEmbed_eq_coeReal_of_time_zero {x : Fin 4 → ℝ} (hx : x 0 = 0) :
    wickEmbed x = fun μ => (x μ : ℂ) := by
  ext μ
  fin_cases μ
  · simp [wickEmbed, hx]
  · simp [wickEmbed]
  · simp [wickEmbed]
  · simp [wickEmbed]

lemma wickEmbedN_eq_coeReal_of_time_zero (n : ℕ) {x : Fin n → Fin 4 → ℝ}
    (hx : ∀ i, x i 0 = 0) :
    wickEmbedN n x = coeReal n x := by
  ext i μ
  exact congrFun (wickEmbed_eq_coeReal_of_time_zero (hx i)) μ

lemma is_spacelike_of_time_zero_ne_zero {v : Fin 4 → ℝ}
    (hv0 : v 0 = 0) (hv : v ≠ 0) :
    is_spacelike v := by
  dsimp [is_spacelike]
  rw [minkowskiInner_explicit, hv0]
  have h_sum_pos : 0 < v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2 := by
    by_contra h_le
    push Not at h_le
    have h1 : v 1 = 0 := by nlinarith [sq_nonneg (v 1), sq_nonneg (v 2), sq_nonneg (v 3)]
    have h2 : v 2 = 0 := by nlinarith [sq_nonneg (v 1), sq_nonneg (v 2), sq_nonneg (v 3)]
    have h3 : v 3 = 0 := by nlinarith [sq_nonneg (v 1), sq_nonneg (v 2), sq_nonneg (v 3)]
    apply hv
    ext μ
    fin_cases μ
    · exact hv0
    · exact h1
    · exact h2
    · exact h3
  linarith

lemma equal_time_mem_jost_points_n (n : ℕ) {x : Fin n → Fin 4 → ℝ}
    (hx0 : ∀ i : Fin n, x i 0 = 0)
    (h_hull : (0 : Fin 4 → ℝ) ∉ jost_convex_hull n x) :
    x ∈ jost_points_n n := by
  intro v hv
  have hv0 : v 0 = 0 := by
    have h_diff_zero : ∀ w ∈ jost_differences_n n x, w 0 = 0 := by
      rintro w ⟨i, hi, rfl⟩
      simp [hx0]
    have h_sub : jost_differences_n n x ⊆ {w : Fin 4 → ℝ | w 0 = 0} := h_diff_zero
    have h_conv : Convex ℝ {w : Fin 4 → ℝ | w 0 = 0} := by
      intro a ha b hb c d _ _ _
      change c * a 0 + d * b 0 = 0
      rw [ha, hb]
      ring
    exact convexHull_min h_sub h_conv hv
  have hv_ne : v ≠ 0 := fun h_eq => h_hull (h_eq ▸ hv)
  exact is_spacelike_of_time_zero_ne_zero hv0 hv_ne

lemma wickEmbedN_equal_time_mem_extended_tube_n {n : ℕ} (hn : 1 < n)
    {x : Fin n → Fin 4 → ℝ} (hx0 : ∀ i : Fin n, x i 0 = 0)
    (h_hull : (0 : Fin 4 → ℝ) ∉ jost_convex_hull n x) :
    wickEmbedN n x ∈ extended_tube_n n := by
  rw [wickEmbedN_eq_coeReal_of_time_zero n hx0]
  exact (jost_theorem n x hn).mp (equal_time_mem_jost_points_n n hx0 h_hull)

noncomputable def su2ToSL2CHom : SU2 →* SL2C where
  toFun := su2ToSL2C
  map_one' := by
    apply Subtype.ext
    rfl
  map_mul' U V := by
    apply Subtype.ext
    rfl

@[simp]
lemma su2ToSL2CHom_apply (U : SU2) : su2ToSL2CHom U = su2ToSL2C U := rfl

@[simp]
lemma su2ToSL2C_one : su2ToSL2C 1 = 1 := su2ToSL2CHom.map_one

@[simp]
lemma su2ToSL2C_mul (U V : SU2) :
    su2ToSL2C (U * V) = su2ToSL2C U * su2ToSL2C V :=
  su2ToSL2CHom.map_mul U V

@[simp]
lemma su2ToSL2C_inv (U : SU2) :
    su2ToSL2C U⁻¹ = (su2ToSL2C U)⁻¹ :=
  su2ToSL2CHom.map_inv U

lemma su2_conjTranspose_eq_adjugate (U : SU2) :
    U.valᴴ = U.val.adjugate := by
  have h_unit : star U.val * U.val = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp (Matrix.mem_specialUnitaryGroup_iff.mp U.property).1
  have h_det : U.val.det = 1 :=
    (Matrix.mem_specialUnitaryGroup_iff.mp U.property).2
  calc
    U.valᴴ = star U.val * 1 := (Matrix.mul_one _).symm
    _ = star U.val * (U.val * U.val.adjugate) := by
      rw [Matrix.mul_adjugate, h_det, one_smul]
    _ = (star U.val * U.val) * U.val.adjugate := (Matrix.mul_assoc _ _ _).symm
    _ = U.val.adjugate := by rw [h_unit, Matrix.one_mul]

lemma su2_transpose_conjTranspose_eq_adjugate_transpose (V : SU2) :
    (V.valᵀ)ᴴ = (V.valᵀ).adjugate := by
  have h1 : (V.valᵀ)ᴴ = (V.valᴴ)ᵀ := by
    ext i j
    simp [Matrix.conjTranspose_apply, Matrix.transpose_apply]
  rw [h1, su2_conjTranspose_eq_adjugate V, Matrix.adjugate_transpose]

def wickUnembed (z : Fin 4 → ℂ) : Fin 4 → ℝ :=
  fun μ => if μ = 0 then (z 0).im else (z μ).re

@[simp]
lemma wickUnembed_wickEmbed (x : Fin 4 → ℝ) :
    wickUnembed (wickEmbed x) = x := by
  ext μ
  fin_cases μ <;> simp [wickUnembed, wickEmbed]

lemma vec_to_spinor_wick_condition_iff (z : Fin 4 → ℂ) :
    (vec_to_spinor z)ᴴ = -(vec_to_spinor z).adjugate ↔
      wickEmbed (wickUnembed z) = z := by
  constructor
  · intro h
    have h00 := congrFun (congrFun h 0) 0
    have h01 := congrFun (congrFun h 0) 1
    have h10 := congrFun (congrFun h 1) 0
    have h11 := congrFun (congrFun h 1) 1
    simp only [Matrix.conjTranspose_apply, Matrix.neg_apply, adjugate_fin_two,
      of_apply, cons_val', cons_val_zero, cons_val_fin_one, cons_val_one,
      vec_to_spinor_apply_00, vec_to_spinor_apply_01,
      vec_to_spinor_apply_10, vec_to_spinor_apply_11,
      star_add, star_sub, star_mul, Complex.star_def, Complex.conj_I] at h00 h01 h10 h11
    have hz0 : (starRingEnd ℂ) (z 0) = -z 0 := by linear_combination (h00 + h11) / 2
    have hz3 : (starRingEnd ℂ) (z 3) = z 3 := by linear_combination (h00 - h11) / 2
    have hz1 : (starRingEnd ℂ) (z 1) = z 1 := by linear_combination (h01 + h10) / 2
    have hz2 : (starRingEnd ℂ) (z 2) = z 2 := by
      have hI : (starRingEnd ℂ) (z 2) * Complex.I = z 2 * Complex.I := by
        linear_combination (h10 - h01) / 2
      have hI' := congrArg (· * Complex.I) hI
      simpa [mul_assoc, Complex.I_mul_I] using hI'
    ext μ
    fin_cases μ
    · dsimp [wickEmbed, wickUnembed]
      apply Complex.ext
      · have hre := congrArg Complex.re hz0
        simp at hre ⊢
        linarith
      · simp
    · dsimp [wickEmbed, wickUnembed]
      apply Complex.ext
      · simp
      · have him := congrArg Complex.im hz1
        simp at him ⊢
        linarith
    · dsimp [wickEmbed, wickUnembed]
      apply Complex.ext
      · simp
      · have him := congrArg Complex.im hz2
        simp at him ⊢
        linarith
    · dsimp [wickEmbed, wickUnembed]
      apply Complex.ext
      · simp
      · have him := congrArg Complex.im hz3
        simp at him ⊢
        linarith
  · intro hz
    rw [← hz]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [vec_to_spinor, wickEmbed, adjugate_fin_two, sigma_0, sigma_1, sigma_2, sigma_3,
        Matrix.conjTranspose_apply] <;> ring

lemma vec_to_spinor_wickEmbed_conjTranspose (x : Fin 4 → ℝ) :
    (vec_to_spinor (wickEmbed x))ᴴ = -(vec_to_spinor (wickEmbed x)).adjugate := by
  rw [vec_to_spinor_wick_condition_iff, wickUnembed_wickEmbed]

lemma spinorPhi_su2_preserves_wick (U V : SU2) (x : Fin 4 → ℝ) :
    wickEmbed (wickUnembed (spinorPhi (su2ToSL2C U, su2ToSL2C V) • wickEmbed x)) =
      spinorPhi (su2ToSL2C U, su2ToSL2C V) • wickEmbed x := by
  rw [← vec_to_spinor_wick_condition_iff]
  have h_act : vec_to_spinor (spinorPhi (su2ToSL2C U, su2ToSL2C V) • wickEmbed x) =
      U.val * vec_to_spinor (wickEmbed x) * V.valᵀ := by
    change vec_to_spinor (spinorPhi_matrix (su2ToSL2C U) (su2ToSL2C V) *ᵥ wickEmbed x) = _
    rw [spinorPhi_matrix_mulVec]
    simp [spinor_action, vec_to_spinor_right_inv, su2ToSL2C]
  rw [h_act]
  have hX := vec_to_spinor_wickEmbed_conjTranspose x
  have h_adj : (U.val * vec_to_spinor (wickEmbed x) * V.valᵀ).adjugate =
      (V.valᵀ).adjugate * ((vec_to_spinor (wickEmbed x)).adjugate * U.val.adjugate) := by
    rw [Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib]
  calc
    (U.val * vec_to_spinor (wickEmbed x) * V.valᵀ)ᴴ
      = (V.valᵀ)ᴴ * (vec_to_spinor (wickEmbed x))ᴴ * U.valᴴ := by
        simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = (V.valᵀ).adjugate * (-(vec_to_spinor (wickEmbed x)).adjugate) * U.val.adjugate := by
        rw [su2_transpose_conjTranspose_eq_adjugate_transpose V, hX,
          su2_conjTranspose_eq_adjugate U]
    _ = -((V.valᵀ).adjugate * ((vec_to_spinor (wickEmbed x)).adjugate * U.val.adjugate)) := by
        simp [Matrix.mul_assoc]
    _ = -(U.val * vec_to_spinor (wickEmbed x) * V.valᵀ).adjugate := by
        rw [h_adj]

noncomputable def euclidRotApply (U V : SU2) (x : Fin 4 → ℝ) : Fin 4 → ℝ :=
  wickUnembed (spinorPhi (su2ToSL2C U, su2ToSL2C V) • wickEmbed x)

@[simp]
theorem wickEmbed_euclidRotApply (U V : SU2) (x : Fin 4 → ℝ) :
    wickEmbed (euclidRotApply U V x) =
      spinorPhi (su2ToSL2C U, su2ToSL2C V) • wickEmbed x :=
  spinorPhi_su2_preserves_wick U V x

@[simp]
lemma euclidRotApply_one (x : Fin 4 → ℝ) :
    euclidRotApply 1 1 x = x := by
  apply wickEmbed_injective
  rw [wickEmbed_euclidRotApply]
  have h1 : (su2ToSL2C 1, su2ToSL2C 1) = (1 : SL2C × SL2C) := by
    ext <;> rfl
  rw [h1, map_one]
  exact Matrix.one_mulVec (wickEmbed x)

lemma euclidRotApply_mul (U₁ U₂ V₁ V₂ : SU2) (x : Fin 4 → ℝ) :
    euclidRotApply (U₁ * U₂) (V₁ * V₂) x =
      euclidRotApply U₁ V₁ (euclidRotApply U₂ V₂ x) := by
  apply wickEmbed_injective
  rw [wickEmbed_euclidRotApply, wickEmbed_euclidRotApply, wickEmbed_euclidRotApply]
  have h_mul : (su2ToSL2C (U₁ * U₂), su2ToSL2C (V₁ * V₂)) =
      (su2ToSL2C U₁, su2ToSL2C V₁) * (su2ToSL2C U₂, su2ToSL2C V₂) := by
    ext <;> rfl
  rw [h_mul, map_mul]
  exact (Matrix.mulVec_mulVec (wickEmbed x) _ _).symm

@[simp]
lemma euclidRotApply_inv_self (U V : SU2) (x : Fin 4 → ℝ) :
    euclidRotApply U⁻¹ V⁻¹ (euclidRotApply U V x) = x := by
  rw [← euclidRotApply_mul, inv_mul_cancel, inv_mul_cancel, euclidRotApply_one]

@[simp]
lemma euclidRotApply_self_inv (U V : SU2) (x : Fin 4 → ℝ) :
    euclidRotApply U V (euclidRotApply U⁻¹ V⁻¹ x) = x := by
  rw [← euclidRotApply_mul, mul_inv_cancel, mul_inv_cancel, euclidRotApply_one]

lemma euclidRotApply_add (U V : SU2) (x y : Fin 4 → ℝ) :
    euclidRotApply U V (x + y) = euclidRotApply U V x + euclidRotApply U V y := by
  apply wickEmbed_injective
  rw [wickEmbed_euclidRotApply, wickEmbed_add, wickEmbed_add,
    wickEmbed_euclidRotApply, wickEmbed_euclidRotApply]
  exact Matrix.mulVec_add _ _ _

lemma euclidRotApply_smul (U V : SU2) (c : ℝ) (x : Fin 4 → ℝ) :
    euclidRotApply U V (c • x) = c • euclidRotApply U V x := by
  apply wickEmbed_injective
  rw [wickEmbed_euclidRotApply, wickEmbed_smul, wickEmbed_smul, wickEmbed_euclidRotApply]
  change (spinorPhi (su2ToSL2C U, su2ToSL2C V)).val.val *ᵥ ((c : ℂ) • wickEmbed x) =
    (c : ℂ) • ((spinorPhi (su2ToSL2C U, su2ToSL2C V)).val.val *ᵥ wickEmbed x)
  exact Matrix.mulVec_smul _ _ _

noncomputable def euclidRotLM (U V : SU2) : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ) where
  toFun := euclidRotApply U V
  map_add' := euclidRotApply_add U V
  map_smul' c v := by
    simp only [RingHom.id_apply]
    exact euclidRotApply_smul U V c v

theorem euclidInner_euclidRotApply (U V : SU2) (x y : Fin 4 → ℝ) :
    euclidInner (euclidRotApply U V x) (euclidRotApply U V y) = euclidInner x y := by
  apply Complex.ofReal_injective
  rw [← neg_inj]
  rw [← minkowskiInnerC_wickEmbed, ← minkowskiInnerC_wickEmbed]
  rw [wickEmbed_euclidRotApply, wickEmbed_euclidRotApply]
  exact complex_lorentz_preserves_inner_pair
    (spinorPhi (su2ToSL2C U, su2ToSL2C V)) (wickEmbed x) (wickEmbed y)

noncomputable def euclidRotOfSU2 (U V : SU2) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun μ ν => euclidRotLM U V (Pi.single ν 1) μ

lemma euclidRotOfSU2_mulVec (U V : SU2) (x : Fin 4 → ℝ) :
    (euclidRotOfSU2 U V).mulVec x = euclidRotApply U V x := by
  have hx : x = ∑ ν : Fin 4, x ν • Pi.single ν (1 : ℝ) := by
    ext μ
    simp [Finset.sum_apply, Pi.single_apply]
  change (euclidRotOfSU2 U V).mulVec x = euclidRotLM U V x
  conv_rhs => rw [hx]
  rw [map_sum]
  ext μ
  rw [Finset.sum_apply]
  dsimp [Matrix.mulVec, dotProduct, euclidRotOfSU2]
  refine Finset.sum_congr rfl (fun ν _ => ?_)
  rw [map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]

@[simp]
theorem wickEmbed_euclidRotOfSU2_mulVec (U V : SU2) (x : Fin 4 → ℝ) :
    wickEmbed ((euclidRotOfSU2 U V).mulVec x) =
      spinorPhi (su2ToSL2C U, su2ToSL2C V) • wickEmbed x := by
  rw [euclidRotOfSU2_mulVec, wickEmbed_euclidRotApply]

@[simp]
lemma euclidRotOfSU2_one :
    euclidRotOfSU2 1 1 = 1 := by
  ext μ ν
  have h := congrFun (euclidRotOfSU2_mulVec 1 1 (Pi.single ν 1)) μ
  rw [euclidRotApply_one] at h
  have h1 : (euclidRotOfSU2 1 1).mulVec (Pi.single ν 1) μ = euclidRotOfSU2 1 1 μ ν := by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [h1] at h
  rw [h, Matrix.one_apply]
  simp [Pi.single_apply]

lemma euclidRotOfSU2_mul (U₁ U₂ V₁ V₂ : SU2) :
    euclidRotOfSU2 (U₁ * U₂) (V₁ * V₂) =
      euclidRotOfSU2 U₁ V₁ * euclidRotOfSU2 U₂ V₂ := by
  apply Matrix.ext_of_mulVec_single
  intro ν
  rw [← Matrix.mulVec_mulVec, euclidRotOfSU2_mulVec, euclidRotOfSU2_mulVec,
    euclidRotOfSU2_mulVec, euclidRotApply_mul]

lemma euclidRotOfSU2_transpose_mul_self (U V : SU2) :
    (euclidRotOfSU2 U V)ᵀ * euclidRotOfSU2 U V = 1 := by
  ext μ ν
  rw [Matrix.mul_apply]
  have h_inner := euclidInner_euclidRotApply U V (Pi.single μ 1) (Pi.single ν 1)
  dsimp [euclidInner, euclidRotOfSU2, euclidRotLM] at h_inner ⊢
  rw [h_inner]
  simp [Pi.single_apply, Matrix.one_apply, eq_comm]

lemma euclidRotOfSU2_mul_transpose_self (U V : SU2) :
    euclidRotOfSU2 U V * (euclidRotOfSU2 U V)ᵀ = 1 :=
  mul_eq_one_comm.mpr (euclidRotOfSU2_transpose_mul_self U V)

noncomputable def euclidAct (a : Fin 4 → ℝ) (U V : SU2) (x : Fin 4 → ℝ) : Fin 4 → ℝ :=
  (euclidRotOfSU2 U V).mulVec x + a

noncomputable def euclidRotN (n : ℕ) (U V : SU2) (x : Fin n → Fin 4 → ℝ) :
    Fin n → Fin 4 → ℝ :=
  fun i => (euclidRotOfSU2 U V).mulVec (x i)

@[simp]
lemma wickEmbedN_euclidRotN (n : ℕ) (U V : SU2) (x : Fin n → Fin 4 → ℝ) :
    wickEmbedN n (euclidRotN n U V x) =
      spinorPhi (su2ToSL2C U, su2ToSL2C V) • wickEmbedN n x := by
  ext i μ
  exact congrFun (wickEmbed_euclidRotOfSU2_mulVec U V (x i)) μ

def negOneSU2 : SU2 :=
  ⟨-1, Matrix.mem_specialUnitaryGroup_iff.mpr
    ⟨by rw [Matrix.mem_unitaryGroup_iff]; simp,
     by rw [Matrix.det_fin_two]; simp⟩⟩

@[simp]
lemma su2ToSL2C_negOneSU2 :
    su2ToSL2C negOneSU2 = (-1 : SL2C) := by
  apply Subtype.ext
  rfl

@[simp]
lemma euclidRotApply_negOne_one (x : Fin 4 → ℝ) :
    euclidRotApply negOneSU2 1 x = -x := by
  apply wickEmbed_injective
  rw [wickEmbed_euclidRotApply, wickEmbed_neg, su2ToSL2C_negOneSU2, su2ToSL2C_one]
  exact spinorPT_smul_vec (wickEmbed x)

@[simp]
lemma euclidRotApply_one_negOne (x : Fin 4 → ℝ) :
    euclidRotApply 1 negOneSU2 x = -x := by
  apply wickEmbed_injective
  rw [wickEmbed_euclidRotApply, wickEmbed_neg, su2ToSL2C_one, su2ToSL2C_negOneSU2,
    spinorPhi_one_neg_one]
  exact spinorPT_smul_vec (wickEmbed x)

@[simp]
lemma euclidRotApply_negOne_negOne (x : Fin 4 → ℝ) :
    euclidRotApply negOneSU2 negOneSU2 x = x := by
  have h1 : negOneSU2 * 1 = negOneSU2 := mul_one _
  have h2 : (1 : SU2) * negOneSU2 = negOneSU2 := one_mul _
  have h' := euclidRotApply_mul negOneSU2 1 1 negOneSU2 x
  rw [h1, h2] at h'
  rw [h', euclidRotApply_one_negOne, euclidRotApply_negOne_one, neg_neg]

lemma boostHalfSL2C_unitary (θ : ℝ) :
    (boostHalfSL2C θ).val * star (boostHalfSL2C θ).val = 1 := by
  rw [boostHalfSL2C_val θ, Matrix.star_eq_conjTranspose]
  have h1 : (starRingEnd ℂ) (Complex.exp (-(Complex.I * (θ : ℂ) / 2))) =
      Complex.exp (Complex.I * (θ : ℂ) / 2) := by
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_neg, map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
    ring
  have h2 : (starRingEnd ℂ) (Complex.exp (Complex.I * (θ : ℂ) / 2)) =
      Complex.exp (-(Complex.I * (θ : ℂ) / 2)) := by
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_div₀, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
    ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
      h1, h2, complex_exp_identity_3, complex_exp_identity_4]

noncomputable def boostHalfSU2 (θ : ℝ) : SU2 :=
  ⟨(boostHalfSL2C θ).val,
   Matrix.mem_specialUnitaryGroup_iff.mpr
     ⟨Matrix.mem_unitaryGroup_iff.mpr (boostHalfSL2C_unitary θ),
      (boostHalfSL2C θ).property⟩⟩

@[simp]
lemma su2ToSL2C_boostHalfSU2 (θ : ℝ) :
    su2ToSL2C (boostHalfSU2 θ) = boostHalfSL2C θ := by
  apply Subtype.ext
  rfl

theorem euclidRotApply_boostHalfSU2 (θ : ℝ) (x : Fin 4 → ℝ) :
    euclidRotApply (boostHalfSU2 θ) (boostHalfSU2 θ) x =
      ![Real.cos θ * x 0 - Real.sin θ * x 3,
        x 1,
        x 2,
        Real.sin θ * x 0 + Real.cos θ * x 3] := by
  apply wickEmbed_injective
  rw [wickEmbed_euclidRotApply, su2ToSL2C_boostHalfSU2]
  change (spinorPhi (boostHalfSL2C θ, boostHalfSL2C θ)).val.val *ᵥ wickEmbed x = _
  rw [spinorPhi_boost_val, ← spinorPhi_boost_matrix, spinorPhi_boost_mulVec]
  ext μ
  fin_cases μ
  · dsimp [wickEmbed]
    push_cast
    ring_nf
  · dsimp [wickEmbed]
  · dsimp [wickEmbed]
  · dsimp [wickEmbed]
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def TubeTranslationInvariant {W : WightmanFamily ι} (E : TubeExtension W) : Prop :=
  ∀ (n : ℕ) (α : Fin n → ι) (z : Fin n → Fin 4 → ℂ) (a : Fin 4 → ℂ),
    z ∈ forward_tube_n n →
    E.H n α (fun i => z i + a) = E.H n α z

def TubeWickHermiticity {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    {W : WightmanFamily ι} (E : TubeExtension W) : Prop :=
  ∀ (n : ℕ) (α : Fin n → ι) (z : Fin n → Fin 4 → ℂ),
    z ∈ forward_tube_n n →
    (fun i μ => star (z (Fin.rev i) μ)) ∈ forward_tube_n n →
    star (E.H n α z) =
      ∑ β : Fin n → ι,
        (∏ i, S.C (α i) (β i)) * E.H n (β ∘ Fin.rev) (fun i μ => star (z (Fin.rev i) μ))

noncomputable def schwingerFromTube {W : WightmanFamily ι} (E : TubeExtension W)
    (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ) : ℂ :=
  E.H n α (wickEmbedN n x)

noncomputable def vladimirovSchwinger (W : WightmanFamily ι)
    (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ) : ℂ :=
  vladimirov_H W n α (wickEmbedN n x)

@[simp]
lemma schwingerFromTube_vladimirov (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (hspec : SpectrumCondition W) (hP : PoincareCovariant R W)
    (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ) :
    schwingerFromTube (vladimirovTubeExtension R W hspec hP) n α x =
      vladimirovSchwinger W n α x := rfl

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirovSchwinger_eq_zero_eval {W : WightmanFamily ι} (hspec : SpectrumCondition W)
    (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ) :
    vladimirovSchwinger W n α x = vladimirov_H W n α 0 :=
  vladimirov_H_eq_zero_eval hspec n α (wickEmbedN n x)

omit [Fintype ι] [DecidableEq ι] in
theorem schwingerFromTube_contDiffOn {W : WightmanFamily ι} (E : TubeExtension W)
    (n : ℕ) (α : Fin n → ι) :
    ContDiffOn ℝ (⊤ : ℕ∞) (schwingerFromTube E n α) (orderedEuclidN n) := by
  have h_holo : ContDiffOn ℂ (⊤ : ℕ∞) (E.H n α) (forward_tube_n n) :=
    (E.analytic n α).contDiffOn (forward_tube_n_isOpen n).uniqueDiffOn
  have h_real : ContDiffOn ℝ (⊤ : ℕ∞) (E.H n α) (forward_tube_n n) :=
    h_holo.restrict_scalars ℝ
  have h_wick : ContDiffOn ℝ (⊤ : ℕ∞) (wickEmbedN n) (orderedEuclidN n) :=
    (wickEmbedNCLM n).contDiff.contDiffOn
  exact h_real.comp h_wick (fun x hx => wickEmbedN_mem_forward_tube_n n hx)

theorem vladimirovSchwinger_contDiffOn (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (hspec : SpectrumCondition W) (hP : PoincareCovariant R W)
    (n : ℕ) (α : Fin n → ι) :
    ContDiffOn ℝ (⊤ : ℕ∞) (vladimirovSchwinger W n α) (orderedEuclidN n) :=
  schwingerFromTube_contDiffOn (vladimirovTubeExtension R W hspec hP) n α

omit [Fintype ι] [DecidableEq ι] in
theorem schwingerFromTube_translation_invariant {W : WightmanFamily ι} (E : TubeExtension W)
    (htrans : TubeTranslationInvariant E) (n : ℕ) (α : Fin n → ι)
    (x : Fin n → Fin 4 → ℝ) (hx : x ∈ orderedEuclidN n) (a : Fin 4 → ℝ) :
    schwingerFromTube E n α (fun i => x i + a) = schwingerFromTube E n α x := by
  dsimp [schwingerFromTube]
  have h_add : wickEmbedN n (fun i => x i + a) =
      fun i => wickEmbedN n x i + wickEmbed a := by
    ext i μ
    exact congrFun (wickEmbed_add (x i) a) μ
  rw [h_add]
  exact htrans n α (wickEmbedN n x) (wickEmbed a) (wickEmbedN_mem_forward_tube_n n hx)

lemma vladimirov_tubeTranslationInvariant (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (hspec : SpectrumCondition W) (hP : PoincareCovariant R W) :
    TubeTranslationInvariant (vladimirovTubeExtension R W hspec hP) := by
  intro n α z a _hz
  change vladimirov_H W n α (fun i => z i + a) = vladimirov_H W n α z
  rw [vladimirov_H_eq_zero_eval hspec n α (fun i => z i + a),
      vladimirov_H_eq_zero_eval hspec n α z]

omit [Fintype ι] [DecidableEq ι] in
theorem vladimirovSchwinger_translation_invariant {W : WightmanFamily ι}
    (hspec : SpectrumCondition W) (n : ℕ) (α : Fin n → ι)
    (x : Fin n → Fin 4 → ℝ) (a : Fin 4 → ℝ) :
    vladimirovSchwinger W n α (fun i => x i + a) = vladimirovSchwinger W n α x := by
  rw [vladimirovSchwinger_eq_zero_eval hspec, vladimirovSchwinger_eq_zero_eval hspec]

theorem schwingerFromTube_euclidCovariant (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (E : TubeExtension W) (h_cov : TubeCovariant R E)
    (n : ℕ) (U V : SU2) (x : Fin n → Fin 4 → ℝ)
    (hx : x ∈ orderedEuclidN n) (hRx : euclidRotN n U V x ∈ orderedEuclidN n)
    (α : Fin n → ι) :
    schwingerFromTube E n α (euclidRotN n U V x) =
      ∑ β : Fin n → ι,
        (∏ i, R.σ (su2ToSL2C U, su2ToSL2C V) (α i) (β i)) *
          schwingerFromTube E n β x := by
  have h_ccov : ComplexCovariant R E := complex_covariance_of_real R W E h_cov
  dsimp [schwingerFromTube]
  rw [wickEmbedN_euclidRotN]
  have hz : wickEmbedN n x ∈ forward_tube_n n := wickEmbedN_mem_forward_tube_n n hx
  have hRz : spinorPhi (su2ToSL2C U, su2ToSL2C V) • wickEmbedN n x ∈ forward_tube_n n := by
    rw [← wickEmbedN_euclidRotN]
    exact wickEmbedN_mem_forward_tube_n n hRx
  exact h_ccov n (su2ToSL2C U) (su2ToSL2C V) (wickEmbedN n x) hz hRz α

theorem vladimirovSchwinger_euclidCovariant (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (hspec : SpectrumCondition W) (hP : PoincareCovariant R W)
    (n : ℕ) (U V : SU2) (x : Fin n → Fin 4 → ℝ) (α : Fin n → ι) :
    vladimirovSchwinger W n α (euclidRotN n U V x) =
      ∑ β : Fin n → ι,
        (∏ i, R.σ (su2ToSL2C U, su2ToSL2C V) (α i) (β i)) *
          vladimirovSchwinger W n β x := by
  dsimp [vladimirovSchwinger]
  exact vladimirov_H_complexCovariant_all R W hspec hP n
    (su2ToSL2C U) (su2ToSL2C V)
    (wickEmbedN n (euclidRotN n U V x)) (wickEmbedN n x) α

theorem schwingerFromTube_os_hermiticity {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    {W : WightmanFamily ι} (E : TubeExtension W) (hherm : TubeWickHermiticity S E)
    (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ) (hx : x ∈ orderedEuclidN n) :
    star (schwingerFromTube E n α x) =
      ∑ β : Fin n → ι,
        (∏ i, S.C (α i) (β i)) *
          schwingerFromTube E n (β ∘ Fin.rev) (euclidTimeReflectRev n x) := by
  dsimp [schwingerFromTube]
  rw [wickEmbedN_euclidTimeReflectRev]
  have hz : wickEmbedN n x ∈ forward_tube_n n := wickEmbedN_mem_forward_tube_n n hx
  have h_star_z : (fun i μ => star (wickEmbedN n x (Fin.rev i) μ)) ∈ forward_tube_n n := by
    rw [← wickEmbedN_euclidTimeReflectRev]
    exact wickEmbedN_mem_forward_tube_n n (euclidTimeReflectRev_mem_orderedEuclidN n hx)
  exact hherm n α (wickEmbedN n x) hz h_star_z

omit [Fintype ι] [DecidableEq ι] in
theorem schwingerFromTube_weakLocality {W : WightmanFamily ι} {η : ℂ}
    (E : TubeExtension W) (hloc : TubeWeakLocality η E)
    (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ) (hx : x ∈ orderedEuclidN n) :
    schwingerFromTube E n α (-(x ∘ Fin.rev)) =
      η ^ (n * (n - 1) / 2) * schwingerFromTube E n (α ∘ Fin.rev) x := by
  dsimp [schwingerFromTube]
  rw [wickEmbedN_neg, wickEmbedN_comp_rev]
  exact hloc n α (wickEmbedN n x) (wickEmbedN_mem_forward_tube_n n hx)

theorem vladimirovSchwinger_weakLocality_iff (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    {η : ℂ} (hspec : SpectrumCondition W) (hP : PoincareCovariant R W) :
    WeakLocality η W ↔
      ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
        x ∈ orderedEuclidN n →
        vladimirovSchwinger W n α (-(x ∘ Fin.rev)) =
          η ^ (n * (n - 1) / 2) * vladimirovSchwinger W n (α ∘ Fin.rev) x := by
  refine (jost_theorem_vladimirov R W hspec hP).trans ?_
  constructor
  · intro h_tloc n α x hx
    exact schwingerFromTube_weakLocality (vladimirovTubeExtension R W hspec hP) h_tloc n α x hx
  · intro h_euclid n α z _hz
    have hx := euclidOrderedBasePoint_mem_orderedEuclidN n
    have h_base := h_euclid n α (euclidOrderedBasePoint n) hx
    dsimp [vladimirovSchwinger] at h_base
    change vladimirov_H W n α (-(z ∘ Fin.rev)) =
      η ^ (n * (n - 1) / 2) * vladimirov_H W n (α ∘ Fin.rev) z
    rw [vladimirov_H_eq_zero_eval hspec n α (-(z ∘ Fin.rev)),
        vladimirov_H_eq_zero_eval hspec n (α ∘ Fin.rev) z]
    rw [vladimirov_H_eq_zero_eval hspec n α
          (wickEmbedN n (-(euclidOrderedBasePoint n ∘ Fin.rev))),
        vladimirov_H_eq_zero_eval hspec n (α ∘ Fin.rev)
          (wickEmbedN n (euclidOrderedBasePoint n))] at h_base
    exact h_base

theorem vladimirovSchwinger_pct_theorem (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    {η : ℂ} (hspec : SpectrumCondition W) (hP : PoincareCovariant R W)
    (hloc : WeakLocality η W)
    (n : ℕ) (x : Fin n → Fin 4 → ℝ) (hx : x ∈ orderedEuclidN n) (α : Fin n → ι) :
    vladimirovSchwinger W n α (-(x ∘ Fin.rev)) =
      η ^ (n * (n - 1) / 2) *
        ∑ β : Fin n → ι,
          (∏ i, R.σ (-1, 1) (α i) (β i)) *
            vladimirovSchwinger W n (β ∘ Fin.rev) x := by
  dsimp [vladimirovSchwinger]
  rw [wickEmbedN_neg, wickEmbedN_comp_rev]
  exact vladimirov_tube_pct_theorem R W hspec hP hloc n
    (wickEmbedN n x) (wickEmbedN_mem_forward_tube_n n hx) α

theorem schwingerFromTube_spin_parity_selection (R : HolomorphicLorentzRep ι)
    (W : WightmanFamily ι) (E : TubeExtension W) (h_cov : TubeCovariant R E)
    {ε : ℂ} (hε : R.HasSpinParity ε)
    (n : ℕ) (x : Fin n → Fin 4 → ℝ) (hx : x ∈ orderedEuclidN n) (α : Fin n → ι) :
    schwingerFromTube E n α x = ε ^ n * schwingerFromTube E n α x :=
  tube_spin_parity_selection R W E h_cov ε hε n
    (wickEmbedN n x) (wickEmbedN_mem_forward_tube_n n hx) α

theorem schwingerFromTube_eq_zero_of_odd_fermion (R : HolomorphicLorentzRep ι)
    (W : WightmanFamily ι) (E : TubeExtension W) (h_cov : TubeCovariant R E)
    (hε : R.HasSpinParity (-1))
    (n : ℕ) (hn : Odd n) (x : Fin n → Fin 4 → ℝ) (hx : x ∈ orderedEuclidN n)
    (α : Fin n → ι) :
    schwingerFromTube E n α x = 0 :=
  tube_eq_zero_of_odd_fermion R W E h_cov hε n hn
    (wickEmbedN n x) (wickEmbedN_mem_forward_tube_n n hx) α

theorem schwinger_spin_statistics_theorem (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    {η ε : ℂ} (E : TubeExtension W)
    (hε : R.HasSpinParity ε)
    (h_tloc : TubeWeakLocality η E) (h_exch : TwoPointSpinExchange ε E)
    (h_nondeg : ∃ (α : Fin 2 → ι) (x : Fin 2 → Fin 4 → ℝ),
      x ∈ orderedEuclidN 2 ∧ schwingerFromTube E 2 (α ∘ Fin.rev) x ≠ 0) :
    η = ε := by
  rcases h_nondeg with ⟨α, x, hx, hne⟩
  exact spin_statistics_theorem_tube R W E hε h_tloc h_exch
    ⟨α, wickEmbedN 2 x, wickEmbedN_mem_forward_tube_n 2 hx, hne⟩

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev SchwingerFamily (ι : Type*) : Type _ :=
  ∀ n : ℕ, (Fin n → ι) → (Fin n → Fin 4 → ℝ) → ℂ

omit [Fintype ι] [DecidableEq ι] in
lemma schwinger_congr_n (𝒮 : SchwingerFamily ι) {n m : ℕ} (h : n = m)
    (α : Fin m → ι) (x : Fin m → Fin 4 → ℝ) :
    𝒮 n (α ∘ finCongr h) (x ∘ finCongr h) = 𝒮 m α x := by
  subst h
  rfl

def osConcatPoint (j k : ℕ) (x : Fin j → Fin 4 → ℝ) (y : Fin k → Fin 4 → ℝ) :
    Fin (j + k) → Fin 4 → ℝ :=
  Fin.append (euclidTimeReflectRev j x) y

def osConcatIdx (j k : ℕ) (β : Fin j → ι) (α' : Fin k → ι) : Fin (j + k) → ι :=
  Fin.append (β ∘ Fin.rev) α'

@[simp]
lemma osConcatPoint_castAdd (j k : ℕ) (x : Fin j → Fin 4 → ℝ) (y : Fin k → Fin 4 → ℝ)
    (i : Fin j) :
    osConcatPoint j k x y (Fin.castAdd k i) = euclidTimeReflect (x (Fin.rev i)) := by
  simp [osConcatPoint, euclidTimeReflectRev]

@[simp]
lemma osConcatPoint_natAdd (j k : ℕ) (x : Fin j → Fin 4 → ℝ) (y : Fin k → Fin 4 → ℝ)
    (i : Fin k) :
    osConcatPoint j k x y (Fin.natAdd j i) = y i := by
  simp [osConcatPoint]

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma osConcatIdx_castAdd (j k : ℕ) (β : Fin j → ι) (α' : Fin k → ι) (i : Fin j) :
    osConcatIdx j k β α' (Fin.castAdd k i) = β (Fin.rev i) := by
  simp [osConcatIdx]

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma osConcatIdx_natAdd (j k : ℕ) (β : Fin j → ι) (α' : Fin k → ι) (i : Fin k) :
    osConcatIdx j k β α' (Fin.natAdd j i) = α' i := by
  simp [osConcatIdx]

lemma fin_append_apply_lt {α : Type*} {j k : ℕ} (u : Fin j → α) (v : Fin k → α)
    (i : Fin (j + k)) (hi : i.val < j) :
    Fin.append u v i = u ⟨i.val, hi⟩ := by
  have h_eq : i = Fin.castAdd k ⟨i.val, hi⟩ := by
    ext
    rfl
  conv_lhs => rw [h_eq]
  exact Fin.append_left u v ⟨i.val, hi⟩

lemma fin_append_apply_ge {α : Type*} {j k : ℕ} (u : Fin j → α) (v : Fin k → α)
    (i : Fin (j + k)) (hi : j ≤ i.val) :
    Fin.append u v i = v ⟨i.val - j, Nat.sub_lt_left_of_lt_add hi i.isLt⟩ := by
  have h_eq : i = Fin.natAdd j ⟨i.val - j, Nat.sub_lt_left_of_lt_add hi i.isLt⟩ := by
    ext
    dsimp
    omega
  conv_lhs => rw [h_eq]
  exact Fin.append_right u v ⟨i.val - j, Nat.sub_lt_left_of_lt_add hi i.isLt⟩

theorem osConcatPoint_mem_orderedEuclidN (j k : ℕ)
    {x : Fin j → Fin 4 → ℝ} (hx : x ∈ posOrderedEuclidN j)
    {y : Fin k → Fin 4 → ℝ} (hy : y ∈ posOrderedEuclidN k) :
    osConcatPoint j k x y ∈ orderedEuclidN (j + k) := by
  intro i hi
  dsimp [osConcatPoint]
  have h_left_ord : euclidTimeReflectRev j x ∈ orderedEuclidN j :=
    euclidTimeReflectRev_mem_orderedEuclidN j hx.2
  by_cases h1 : i.val + 1 < j
  · have h0 : i.val < j := by omega
    rw [fin_append_apply_lt _ _ i h0, fin_append_apply_lt _ _ ⟨i.val + 1, hi⟩ h1]
    exact h_left_ord ⟨i.val, h0⟩ h1
  · by_cases h0 : i.val < j
    · have h_ge : j ≤ (⟨i.val + 1, hi⟩ : Fin (j + k)).val := by
        dsimp
        omega
      rw [fin_append_apply_lt _ _ i h0, fin_append_apply_ge _ _ ⟨i.val + 1, hi⟩ h_ge]
      have h_neg : euclidTimeReflectRev j x ⟨i.val, h0⟩ 0 < 0 := by
        dsimp [euclidTimeReflectRev, euclidTimeReflect]
        linarith [hx.1 (Fin.rev ⟨i.val, h0⟩)]
      have h_pos : 0 < y ⟨i.val + 1 - j, Nat.sub_lt_left_of_lt_add h_ge hi⟩ 0 :=
        hy.1 _
      linarith
    · have h_ge0 : j ≤ i.val := by omega
      have h_ge1 : j ≤ (⟨i.val + 1, hi⟩ : Fin (j + k)).val := by
        dsimp
        omega
      rw [fin_append_apply_ge _ _ i h_ge0, fin_append_apply_ge _ _ ⟨i.val + 1, hi⟩ h_ge1]
      have h_sub_lt : i.val - j + 1 < k := by omega
      have h_idx_eq : (⟨i.val + 1 - j, Nat.sub_lt_left_of_lt_add h_ge1 hi⟩ : Fin k) =
          ⟨i.val - j + 1, h_sub_lt⟩ := by
        ext
        dsimp
        omega
      rw [h_idx_eq]
      exact hy.2 ⟨i.val - j, Nat.sub_lt_left_of_lt_add h_ge0 i.isLt⟩ h_sub_lt

lemma fin_append_rev_finCongr {α : Type*} (j k : ℕ) (u : Fin k → α) (v : Fin j → α) :
    (Fin.append u v ∘ Fin.rev) ∘ finCongr (Nat.add_comm j k) =
      Fin.append (v ∘ Fin.rev) (u ∘ Fin.rev) := by
  ext i
  simp only [Function.comp_apply]
  by_cases hi : i.val < j
  · rw [fin_append_apply_lt _ _ i hi]
    have h_rev_ge : k ≤ (Fin.rev (finCongr (Nat.add_comm j k) i)).val := by
      dsimp [Fin.rev, finCongr]
      omega
    rw [fin_append_apply_ge _ _ (Fin.rev (finCongr (Nat.add_comm j k) i)) h_rev_ge]
    have h_idx : (⟨(Fin.rev (finCongr (Nat.add_comm j k) i)).val - k,
        Nat.sub_lt_left_of_lt_add h_rev_ge
          (Fin.rev (finCongr (Nat.add_comm j k) i)).isLt⟩ : Fin j) =
        Fin.rev ⟨i.val, hi⟩ := by
      ext
      dsimp [Fin.rev, finCongr]
      omega
    rw [h_idx]
    rfl
  · have h_ge : j ≤ i.val := by omega
    rw [fin_append_apply_ge _ _ i h_ge]
    have h_rev_lt : (Fin.rev (finCongr (Nat.add_comm j k) i)).val < k := by
      dsimp [Fin.rev, finCongr]
      omega
    rw [fin_append_apply_lt _ _ (Fin.rev (finCongr (Nat.add_comm j k) i)) h_rev_lt]
    have h_idx : (⟨(Fin.rev (finCongr (Nat.add_comm j k) i)).val, h_rev_lt⟩ : Fin k) =
        Fin.rev ⟨i.val - j, Nat.sub_lt_left_of_lt_add h_ge i.isLt⟩ := by
      ext
      dsimp [Fin.rev, finCongr]
      omega
    rw [h_idx]
    rfl

lemma euclidTimeReflectRev_osConcatPoint (j k : ℕ)
    (x : Fin j → Fin 4 → ℝ) (y : Fin k → Fin 4 → ℝ) :
    euclidTimeReflectRev (k + j) (osConcatPoint k j y x) ∘ finCongr (Nat.add_comm j k) =
      osConcatPoint j k x y := by
  have h1 : euclidTimeReflectRev (k + j) (osConcatPoint k j y x) =
      Fin.append (euclidTimeReflect ∘ euclidTimeReflectRev k y)
        (euclidTimeReflect ∘ x) ∘ Fin.rev := by
    ext m μ
    dsimp [euclidTimeReflectRev, osConcatPoint]
    by_cases hm : (Fin.rev m).val < k
    · rw [fin_append_apply_lt _ _ (Fin.rev m) hm, fin_append_apply_lt _ _ (Fin.rev m) hm]
      rfl
    · have h_ge : k ≤ (Fin.rev m).val := by omega
      rw [fin_append_apply_ge _ _ (Fin.rev m) h_ge, fin_append_apply_ge _ _ (Fin.rev m) h_ge]
      rfl
  rw [h1, fin_append_rev_finCongr]
  dsimp [osConcatPoint]
  congr 1
  ext i μ
  simp [euclidTimeReflectRev, Fin.rev_rev]

omit [Fintype ι] [DecidableEq ι] in
lemma osConcatIdx_rev_finCongr (j k : ℕ) (α : Fin j → ι) (β' : Fin k → ι) :
    (osConcatIdx k j β' α ∘ Fin.rev) ∘ finCongr (Nat.add_comm j k) =
      osConcatIdx j k α β' := by
  dsimp [osConcatIdx]
  rw [fin_append_rev_finCongr]
  congr 1
  ext i
  simp [Fin.rev_rev]

def osConcatIdxEquiv (k j : ℕ) : ((Fin k → ι) × (Fin j → ι)) ≃ (Fin (k + j) → ι) where
  toFun p := osConcatIdx k j p.1 p.2
  invFun δ := (fun i => δ (Fin.castAdd j (Fin.rev i)), fun i => δ (Fin.natAdd k i))
  left_inv p := by
    ext i
    · simp [Fin.rev_rev]
    · simp
  right_inv δ := by
    ext m
    dsimp
    by_cases hm : m.val < k
    · have h_eq : m = Fin.castAdd j ⟨m.val, hm⟩ := by ext; rfl
      rw [h_eq, osConcatIdx_castAdd, Fin.rev_rev]
    · have h_ge : k ≤ m.val := by omega
      have h_eq : m = Fin.natAdd k ⟨m.val - k, Nat.sub_lt_left_of_lt_add h_ge m.isLt⟩ := by
        ext; dsimp; omega
      rw [h_eq, osConcatIdx_natAdd]

omit [Fintype ι] [DecidableEq ι] in
lemma prod_osConcatIdx (k j : ℕ) (F : ι → ι → ℂ)
    (γ δL : Fin k → ι) (α β : Fin j → ι) :
    (∏ m : Fin (k + j), F (osConcatIdx k j γ α m) (osConcatIdx k j δL β m)) =
      (∏ i : Fin k, F (γ i) (δL i)) * (∏ r : Fin j, F (α r) (β r)) := by
  rw [Fin.prod_univ_add]
  congr 1
  · simp only [osConcatIdx_castAdd]
    exact Equiv.prod_comp Fin.revPerm (fun i => F (γ i) (δL i))
  · simp only [osConcatIdx_natAdd]

lemma starStructure_map_star_mul_self {R : HolomorphicLorentzRep ι} (S : StarStructure R) :
    S.C.map star * S.C = 1 :=
  mul_eq_one_comm.mp S.involutive

lemma sum_prod_star_C_mul_C {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    (k : ℕ) (α' δL : Fin k → ι) :
    (∑ γ : Fin k → ι, ∏ i : Fin k, star (S.C (α' i) (γ i)) * S.C (γ i) (δL i)) =
      if α' = δL then 1 else 0 := by
  have h_ps := (Fintype.prod_sum
    (fun (i : Fin k) (c : ι) => star (S.C (α' i) c) * S.C c (δL i))).symm
  rw [h_ps]
  have h_mat : ∀ i : Fin k,
      (∑ c : ι, star (S.C (α' i) c) * S.C c (δL i)) =
        (S.C.map star * S.C) (α' i) (δL i) := by
    intro i
    simp [Matrix.mul_apply]
  simp_rw [h_mat, starStructure_map_star_mul_self S]
  by_cases h : α' = δL
  · subst h
    simp
  · rw [if_neg h]
    obtain ⟨i, hi⟩ : ∃ i, α' i ≠ δL i := by
      by_contra hc
      push Not at hc
      exact h (funext hc)
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    exact Matrix.one_apply_ne hi

def OSConfig (ι : Type*) : Type _ :=
  Σ n : ℕ, (Fin n → ι) × posOrderedEuclidN n

def osVacuumConfig (ι : Type*) : OSConfig ι :=
  ⟨0, (Fin.elim0, ⟨euclidOrderedBasePoint 0, euclidOrderedBasePoint_mem_posOrderedEuclidN 0⟩)⟩

def osKernel {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    (𝒮 : SchwingerFamily ι) (A B : OSConfig ι) : ℂ :=
  ∑ β : Fin A.1 → ι,
    (∏ i : Fin A.1, S.C (A.2.1 i) (β i)) *
      𝒮 (A.1 + B.1) (osConcatIdx A.1 B.1 β B.2.1)
        (osConcatPoint A.1 B.1 A.2.2.val B.2.2.val)

def OSHermiticity {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    (𝒮 : SchwingerFamily ι) : Prop :=
  ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
    x ∈ orderedEuclidN n →
    star (𝒮 n α x) =
      ∑ β : Fin n → ι,
        (∏ i : Fin n, S.C (α i) (β i)) *
          𝒮 n (β ∘ Fin.rev) (euclidTimeReflectRev n x)

theorem osKernel_conj_symm {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    (𝒮 : SchwingerFamily ι) (hherm : OSHermiticity S 𝒮)
    (A B : OSConfig ι) :
    star (osKernel S 𝒮 B A) = osKernel S 𝒮 A B := by
  rcases A with ⟨j, α, x, hx⟩
  rcases B with ⟨k, α', y, hy⟩
  unfold osKernel
  dsimp only
  rw [star_sum]
  have h_ord : osConcatPoint k j y x ∈ orderedEuclidN (k + j) :=
    osConcatPoint_mem_orderedEuclidN k j hy hx
  have h_term : ∀ γ : Fin k → ι,
      star ((∏ i : Fin k, S.C (α' i) (γ i)) *
        𝒮 (k + j) (osConcatIdx k j γ α) (osConcatPoint k j y x)) =
      ∑ δL : Fin k → ι, ∑ β : Fin j → ι,
        (∏ i : Fin k, star (S.C (α' i) (γ i)) * S.C (γ i) (δL i)) *
          ((∏ r : Fin j, S.C (α r) (β r)) *
            𝒮 (j + k) (osConcatIdx j k β δL) (osConcatPoint j k x y)) := by
    intro γ
    rw [star_mul', star_prod, hherm (k + j) (osConcatIdx k j γ α) (osConcatPoint k j y x) h_ord]
    rw [← (osConcatIdxEquiv k j).sum_comp]
    rw [Fintype.sum_prod_type]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun δL _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun β _ => ?_)
    dsimp [osConcatIdxEquiv]
    rw [prod_osConcatIdx k j (fun a b => S.C a b) γ δL α β]
    have h_schw :
        𝒮 (k + j) (osConcatIdx k j δL β ∘ Fin.rev)
          (euclidTimeReflectRev (k + j) (osConcatPoint k j y x)) =
        𝒮 (j + k) (osConcatIdx j k β δL) (osConcatPoint j k x y) := by
      rw [← schwinger_congr_n 𝒮 (Nat.add_comm j k)]
      rw [osConcatIdx_rev_finCongr, euclidTimeReflectRev_osConcatPoint]
    rw [h_schw]
    have h_prod_mul :
        (∏ x : Fin k, star (S.C (α' x) (γ x))) * (∏ i : Fin k, S.C (γ i) (δL i)) =
          ∏ i : Fin k, star (S.C (α' i) (γ i)) * S.C (γ i) (δL i) :=
      (Finset.prod_mul_distrib (s := Finset.univ)
        (f := fun i : Fin k => star (S.C (α' i) (γ i)))
        (g := fun i : Fin k => S.C (γ i) (δL i))).symm
    calc (∏ x : Fin k, star (S.C (α' x) (γ x))) *
          (((∏ i : Fin k, S.C (γ i) (δL i)) * ∏ r : Fin j, S.C (α r) (β r)) *
            𝒮 (j + k) (osConcatIdx j k β δL) (osConcatPoint j k x y))
      _ = ((∏ x : Fin k, star (S.C (α' x) (γ x))) * (∏ i : Fin k, S.C (γ i) (δL i))) *
            ((∏ r : Fin j, S.C (α r) (β r)) *
              𝒮 (j + k) (osConcatIdx j k β δL) (osConcatPoint j k x y)) := by ring
      _ = (∏ i : Fin k, star (S.C (α' i) (γ i)) * S.C (γ i) (δL i)) *
            ((∏ r : Fin j, S.C (α r) (β r)) *
              𝒮 (j + k) (osConcatIdx j k β δL) (osConcatPoint j k x y)) := by rw [h_prod_mul]
  simp_rw [h_term]
  rw [Finset.sum_comm]
  have h_collapse : ∀ δL : Fin k → ι,
      (∑ γ : Fin k → ι, ∑ β : Fin j → ι,
        (∏ i : Fin k, star (S.C (α' i) (γ i)) * S.C (γ i) (δL i)) *
          ((∏ r : Fin j, S.C (α r) (β r)) *
            𝒮 (j + k) (osConcatIdx j k β δL) (osConcatPoint j k x y))) =
      (if α' = δL then 1 else 0) *
        ∑ β : Fin j → ι,
          (∏ r : Fin j, S.C (α r) (β r)) *
            𝒮 (j + k) (osConcatIdx j k β δL) (osConcatPoint j k x y) := by
    intro δL
    rw [Finset.sum_comm]
    have h_inner : ∀ β : Fin j → ι,
        (∑ γ : Fin k → ι,
          (∏ i : Fin k, star (S.C (α' i) (γ i)) * S.C (γ i) (δL i)) *
            ((∏ r : Fin j, S.C (α r) (β r)) *
              𝒮 (j + k) (osConcatIdx j k β δL) (osConcatPoint j k x y))) =
        (if α' = δL then 1 else 0) *
          ((∏ r : Fin j, S.C (α r) (β r)) *
            𝒮 (j + k) (osConcatIdx j k β δL) (osConcatPoint j k x y)) := by
      intro β
      rw [← Finset.sum_mul, sum_prod_star_C_mul_C S k α' δL]
    simp_rw [h_inner, ← Finset.mul_sum]
  simp_rw [h_collapse]
  simp

def osPreInner {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    (𝒮 : SchwingerFamily ι) (Ψ Φ : OSConfig ι →₀ ℂ) : ℂ :=
  Ψ.sum fun A cA => Φ.sum fun B cB => star cA * cB * osKernel S 𝒮 A B

def OSReflectionPositive {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    (𝒮 : SchwingerFamily ι) : Prop :=
  ∀ Ψ : OSConfig ι →₀ ℂ, 0 ≤ (osPreInner S 𝒮 Ψ Ψ).re

def OSTranslationInvariant (𝒮 : SchwingerFamily ι) : Prop :=
  ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
    x ∈ orderedEuclidN n → ∀ a : Fin 4 → ℝ,
    𝒮 n α (fun i => x i + a) = 𝒮 n α x

structure OSAxioms (R : HolomorphicLorentzRep ι) (S : StarStructure R)
    (η : ℂ) (𝒮 : SchwingerFamily ι) : Prop where
  os0_smooth : ∀ (n : ℕ) (α : Fin n → ι),
    ContDiffOn ℝ (⊤ : ℕ∞) (𝒮 n α) (orderedEuclidN n)
  os1_translation : OSTranslationInvariant 𝒮
  os1_rotation : ∀ (n : ℕ) (U V : SU2) (x : Fin n → Fin 4 → ℝ),
    x ∈ orderedEuclidN n → euclidRotN n U V x ∈ orderedEuclidN n →
    ∀ α : Fin n → ι,
    𝒮 n α (euclidRotN n U V x) =
      ∑ β : Fin n → ι,
        (∏ i : Fin n, R.σ (su2ToSL2C U, su2ToSL2C V) (α i) (β i)) * 𝒮 n β x
  os2_hermiticity : OSHermiticity S 𝒮
  os2_positivity : OSReflectionPositive S 𝒮
  os3_symmetry : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
    x ∈ orderedEuclidN n →
    𝒮 n α (-(x ∘ Fin.rev)) = η ^ (n * (n - 1) / 2) * 𝒮 n (α ∘ Fin.rev) x

theorem schwingerFromTube_osAxioms (R : HolomorphicLorentzRep ι) (S : StarStructure R)
    (W : WightmanFamily ι) {η : ℂ} (E : TubeExtension W)
    (htrans : TubeTranslationInvariant E) (hcov : TubeCovariant R E)
    (hherm : TubeWickHermiticity S E) (hloc : TubeWeakLocality η E)
    (hpos : OSReflectionPositive S (schwingerFromTube E)) :
    OSAxioms R S η (schwingerFromTube E) where
  os0_smooth := schwingerFromTube_contDiffOn E
  os1_translation := schwingerFromTube_translation_invariant E htrans
  os1_rotation := schwingerFromTube_euclidCovariant R W E hcov
  os2_hermiticity := schwingerFromTube_os_hermiticity S E hherm
  os2_positivity := hpos
  os3_symmetry := schwingerFromTube_weakLocality E hloc

structure OSReflectionPositiveData (R : HolomorphicLorentzRep ι) (S : StarStructure R) where
  𝒮 : SchwingerFamily ι
  hermiticity : OSHermiticity S 𝒮
  positivity : OSReflectionPositive S 𝒮

def OSAxioms.toReflectionPositiveData {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {η : ℂ} {𝒮 : SchwingerFamily ι} (hOS : OSAxioms R S η 𝒮) :
    OSReflectionPositiveData R S where
  𝒮 := 𝒮
  hermiticity := hOS.os2_hermiticity
  positivity := hOS.os2_positivity

lemma osPreInner_conj_symm {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (Ψ Φ : OSConfig ι →₀ ℂ) :
    star (osPreInner S D.𝒮 Φ Ψ) = osPreInner S D.𝒮 Ψ Φ := by
  unfold osPreInner
  rw [Finsupp.sum_comm]
  rw [star_finsuppSum]
  refine Finsupp.sum_congr (fun A _ => ?_)
  change star (Φ.sum fun B cB => star cB * Ψ A * osKernel S D.𝒮 B A) =
    Φ.sum fun B cB => star (Ψ A) * cB * osKernel S D.𝒮 A B
  rw [star_finsuppSum]
  refine Finsupp.sum_congr (fun B _ => ?_)
  change star (star (Φ B) * Ψ A * osKernel S D.𝒮 B A) =
    star (Ψ A) * Φ B * osKernel S D.𝒮 A B
  rw [star_mul', star_mul', star_star, osKernel_conj_symm S D.𝒮 D.hermiticity A B]
  ring

lemma osPreInner_add_left {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (Ψ₁ Ψ₂ Φ : OSConfig ι →₀ ℂ) :
    osPreInner S D.𝒮 (Ψ₁ + Ψ₂) Φ = osPreInner S D.𝒮 Ψ₁ Φ + osPreInner S D.𝒮 Ψ₂ Φ := by
  unfold osPreInner
  rw [Finsupp.sum_add_index']
  · intro A
    simp
  · intro A c₁ c₂
    simp [add_mul, Finsupp.sum_add]

lemma osPreInner_smul_left {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (Ψ Φ : OSConfig ι →₀ ℂ) (c : ℂ) :
    osPreInner S D.𝒮 (c • Ψ) Φ = star c * osPreInner S D.𝒮 Ψ Φ := by
  unfold osPreInner
  rw [Finsupp.sum_smul_index]
  · rw [Finsupp.mul_sum]
    refine Finsupp.sum_congr (fun A _ => ?_)
    rw [Finsupp.mul_sum]
    refine Finsupp.sum_congr (fun B _ => ?_)
    rw [star_mul']
    ring
  · intro A
    simp

@[ext]
structure OSPreHilbertSpace {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) where
  ofFinsupp ::
  toFinsupp : OSConfig ι →₀ ℂ

namespace OSPreHilbertSpace

variable {R : HolomorphicLorentzRep ι} {S : StarStructure R}
  (D : OSReflectionPositiveData R S)

instance : Zero (OSPreHilbertSpace D) := ⟨⟨0⟩⟩
instance : Add (OSPreHilbertSpace D) := ⟨fun x y => ⟨x.1 + y.1⟩⟩
instance : Neg (OSPreHilbertSpace D) := ⟨fun x => ⟨-x.1⟩⟩
instance : Sub (OSPreHilbertSpace D) := ⟨fun x y => ⟨x.1 - y.1⟩⟩
instance {M : Type*} [SMul M (OSConfig ι →₀ ℂ)] : SMul M (OSPreHilbertSpace D) :=
  ⟨fun c x => ⟨c • x.1⟩⟩

@[simp] lemma toFinsupp_zero : (0 : OSPreHilbertSpace D).toFinsupp = 0 := rfl
@[simp] lemma toFinsupp_add (x y : OSPreHilbertSpace D) :
    (x + y).toFinsupp = x.toFinsupp + y.toFinsupp := rfl
@[simp] lemma toFinsupp_neg (x : OSPreHilbertSpace D) :
    (-x).toFinsupp = -x.toFinsupp := rfl
@[simp] lemma toFinsupp_sub (x y : OSPreHilbertSpace D) :
    (x - y).toFinsupp = x.toFinsupp - y.toFinsupp := rfl
@[simp] lemma toFinsupp_smul {M : Type*} [SMul M (OSConfig ι →₀ ℂ)]
    (c : M) (x : OSPreHilbertSpace D) :
    (c • x).toFinsupp = c • x.toFinsupp := rfl

instance : AddCommGroup (OSPreHilbertSpace D) :=
  Function.Injective.addCommGroup toFinsupp (fun _ _ => OSPreHilbertSpace.ext)
    rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

instance : Module ℂ (OSPreHilbertSpace D) :=
  Function.Injective.module ℂ ⟨⟨toFinsupp, rfl⟩, fun _ _ => rfl⟩
    (fun _ _ => OSPreHilbertSpace.ext) (fun _ _ => rfl)

def equivFinsupp : OSPreHilbertSpace D ≃ₗ[ℂ] (OSConfig ι →₀ ℂ) where
  toFun := toFinsupp
  invFun := ofFinsupp
  left_inv x := by cases x; rfl
  right_inv f := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance : PreInnerProductSpace.Core ℂ (OSPreHilbertSpace D) where
  inner Ψ Φ := osPreInner S D.𝒮 Ψ.toFinsupp Φ.toFinsupp
  conj_inner_symm Ψ Φ := osPreInner_conj_symm D Ψ.toFinsupp Φ.toFinsupp
  re_inner_nonneg Ψ := D.positivity Ψ.toFinsupp
  add_left Ψ₁ Ψ₂ Φ := osPreInner_add_left D Ψ₁.toFinsupp Ψ₂.toFinsupp Φ.toFinsupp
  smul_left Ψ Φ c := osPreInner_smul_left D Ψ.toFinsupp Φ.toFinsupp c

instance : SeminormedAddCommGroup (OSPreHilbertSpace D) :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := ℂ)

instance : InnerProductSpace ℂ (OSPreHilbertSpace D) :=
  InnerProductSpace.ofCore _

@[simp]
lemma inner_def (Ψ Φ : OSPreHilbertSpace D) :
    ⟪Ψ, Φ⟫_ℂ = osPreInner S D.𝒮 Ψ.toFinsupp Φ.toFinsupp := rfl

end OSPreHilbertSpace

def osBasisPre {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (A : OSConfig ι) : OSPreHilbertSpace D :=
  ⟨Finsupp.single A 1⟩

def osVacuumPre {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) : OSPreHilbertSpace D :=
  osBasisPre D (osVacuumConfig ι)

@[simp]
lemma inner_osBasisPre {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (A B : OSConfig ι) :
    ⟪osBasisPre D A, osBasisPre D B⟫_ℂ = osKernel S D.𝒮 A B := by
  change osPreInner S D.𝒮 (Finsupp.single A 1) (Finsupp.single B 1) = osKernel S D.𝒮 A B
  unfold osPreInner
  simp

theorem osPreHilbert_cauchy_schwarz {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (Ψ Φ : OSPreHilbertSpace D) :
    ‖⟪Ψ, Φ⟫_ℂ‖ ≤ ‖Ψ‖ * ‖Φ‖ :=
  norm_inner_le_norm Ψ Φ

abbrev OSSepQuotient {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) : Type _ :=
  SeparationQuotient (OSPreHilbertSpace D)

abbrev OSHilbert {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) : Type _ :=
  UniformSpace.Completion (OSPreHilbertSpace D)

def toOSHilbert {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) : OSPreHilbertSpace D →L[ℂ] OSHilbert D :=
  UniformSpace.Completion.toComplL

@[simp]
lemma inner_toOSHilbert {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (Ψ Φ : OSPreHilbertSpace D) :
    ⟪toOSHilbert D Ψ, toOSHilbert D Φ⟫_ℂ = ⟪Ψ, Φ⟫_ℂ :=
  UniformSpace.Completion.inner_coe Ψ Φ

@[simp]
lemma norm_toOSHilbert {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (Ψ : OSPreHilbertSpace D) :
    ‖toOSHilbert D Ψ‖ = ‖Ψ‖ :=
  UniformSpace.Completion.norm_coe Ψ

def osBasis {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (A : OSConfig ι) : OSHilbert D :=
  toOSHilbert D (osBasisPre D A)

def osVacuum {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) : OSHilbert D :=
  toOSHilbert D (osVacuumPre D)

@[simp]
lemma inner_osBasis {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (A B : OSConfig ι) :
    ⟪osBasis D A, osBasis D B⟫_ℂ = osKernel S D.𝒮 A B := by
  dsimp [osBasis]
  rw [inner_toOSHilbert, inner_osBasisPre]

def osLiftConfigMap {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (g : OSConfig ι → OSConfig ι) :
    OSPreHilbertSpace D →ₗ[ℂ] OSPreHilbertSpace D :=
  (OSPreHilbertSpace.equivFinsupp D).symm.toLinearMap.comp
    ((Finsupp.lmapDomain ℂ ℂ g).comp (OSPreHilbertSpace.equivFinsupp D).toLinearMap)

@[simp]
lemma toFinsupp_osLiftConfigMap {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (g : OSConfig ι → OSConfig ι)
    (Ψ : OSPreHilbertSpace D) :
    (osLiftConfigMap D g Ψ).toFinsupp = Finsupp.mapDomain g Ψ.toFinsupp := rfl

@[simp]
lemma osLiftConfigMap_id {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) :
    osLiftConfigMap D id = LinearMap.id := by
  ext Ψ : 1
  apply OSPreHilbertSpace.ext
  simp

lemma osLiftConfigMap_comp {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (g₁ g₂ : OSConfig ι → OSConfig ι) :
    osLiftConfigMap D (g₁ ∘ g₂) = (osLiftConfigMap D g₁).comp (osLiftConfigMap D g₂) := by
  ext Ψ : 1
  apply OSPreHilbertSpace.ext
  simp [Finsupp.mapDomain_comp]

@[simp]
lemma osLiftConfigMap_osBasisPre {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (g : OSConfig ι → OSConfig ι) (A : OSConfig ι) :
    osLiftConfigMap D g (osBasisPre D A) = osBasisPre D (g A) := by
  apply OSPreHilbertSpace.ext
  simp [osBasisPre]

lemma inner_osLiftConfigMap {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (g₁ g₂ : OSConfig ι → OSConfig ι)
    (Ψ Φ : OSPreHilbertSpace D) :
    ⟪osLiftConfigMap D g₁ Ψ, osLiftConfigMap D g₂ Φ⟫_ℂ =
      Ψ.toFinsupp.sum fun A cA =>
        Φ.toFinsupp.sum fun B cB =>
          star cA * cB * osKernel S D.𝒮 (g₁ A) (g₂ B) := by
  rw [OSPreHilbertSpace.inner_def, toFinsupp_osLiftConfigMap, toFinsupp_osLiftConfigMap]
  unfold osPreInner
  rw [Finsupp.sum_mapDomain_index (fun _ => by simp)
    (fun _ _ _ => by simp [add_mul, Finsupp.sum_add])]
  refine Finsupp.sum_congr (fun A _ => ?_)
  rw [Finsupp.sum_mapDomain_index (fun _ => by simp)
    (fun _ _ _ => by ring)]

def euclidTimeVec (τ : ℝ) : Fin 4 → ℝ :=
  fun μ => if μ = 0 then τ else 0

@[simp]
lemma euclidTimeVec_zero : euclidTimeVec 0 = 0 := by
  ext μ
  simp [euclidTimeVec]

lemma euclidTimeVec_add (τ₁ τ₂ : ℝ) :
    euclidTimeVec (τ₁ + τ₂) = euclidTimeVec τ₁ + euclidTimeVec τ₂ := by
  ext μ
  by_cases hμ : μ = 0 <;> simp [euclidTimeVec, hμ]

lemma euclidTimeVec_smul (c τ : ℝ) :
    c • euclidTimeVec τ = euclidTimeVec (c * τ) := by
  ext μ
  by_cases hμ : μ = 0 <;> simp [euclidTimeVec, hμ]

@[simp]
lemma euclidTimeReflect_euclidTimeVec (τ : ℝ) :
    euclidTimeReflect (euclidTimeVec τ) = -euclidTimeVec τ := by
  ext μ
  fin_cases μ <;> simp [euclidTimeReflect, euclidTimeVec]

@[simp]
lemma euclidInner_euclidTimeVec_right (x : Fin 4 → ℝ) (τ : ℝ) :
    euclidInner x (euclidTimeVec τ) = x 0 * τ := by
  simp [euclidInner_explicit, euclidTimeVec]

lemma timeShift_mem_posOrderedEuclidN (n : ℕ) {x : Fin n → Fin 4 → ℝ}
    (hx : x ∈ posOrderedEuclidN n) {τ : ℝ} (hτ : 0 ≤ τ) :
    (fun i => x i + euclidTimeVec τ) ∈ posOrderedEuclidN n := by
  refine ⟨fun i => ?_, shift_mem_orderedEuclidN n hx.2 (euclidTimeVec τ)⟩
  simp only [Pi.add_apply, euclidTimeVec, ↓reduceIte]
  linarith [hx.1 i]

def osConfigTimeShift (τ : ℝ) (hτ : 0 ≤ τ) (A : OSConfig ι) : OSConfig ι :=
  ⟨A.1, (A.2.1, ⟨fun i => A.2.2.val i + euclidTimeVec τ,
    timeShift_mem_posOrderedEuclidN A.1 A.2.2.property hτ⟩)⟩

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma osConfigTimeShift_zero (A : OSConfig ι) :
    osConfigTimeShift 0 le_rfl A = A := by
  rcases A with ⟨n, α, x, hx⟩
  dsimp [osConfigTimeShift]
  congr 2
  ext i μ
  simp

omit [Fintype ι] [DecidableEq ι] in
lemma osConfigTimeShift_add (τ₁ τ₂ : ℝ) (h₁ : 0 ≤ τ₁) (h₂ : 0 ≤ τ₂) (A : OSConfig ι) :
    osConfigTimeShift (τ₁ + τ₂) (add_nonneg h₁ h₂) A =
      osConfigTimeShift τ₁ h₁ (osConfigTimeShift τ₂ h₂ A) := by
  rcases A with ⟨n, α, x, hx⟩
  dsimp [osConfigTimeShift]
  congr 2
  ext i μ
  simp [euclidTimeVec_add, add_assoc, add_comm (euclidTimeVec τ₁ μ)]

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma osConfigTimeShift_vacuum (τ : ℝ) (hτ : 0 ≤ τ) :
    osConfigTimeShift τ hτ (osVacuumConfig ι) = osVacuumConfig ι := by
  dsimp [osConfigTimeShift, osVacuumConfig]
  congr 2
  ext i μ
  exact Fin.elim0 i

lemma osConcatPoint_timeShift_add (j k : ℕ) (x : Fin j → Fin 4 → ℝ) (y : Fin k → Fin 4 → ℝ)
    (τ : ℝ) :
    (fun m => osConcatPoint j k (fun i => x i + euclidTimeVec τ) y m + euclidTimeVec τ) =
      osConcatPoint j k x (fun i => y i + euclidTimeVec τ) := by
  ext m μ
  by_cases hm : m.val < j
  · have h_eq : m = Fin.castAdd k ⟨m.val, hm⟩ := by ext; rfl
    rw [h_eq, osConcatPoint_castAdd, osConcatPoint_castAdd]
    rw [euclidTimeReflect_add, euclidTimeReflect_euclidTimeVec]
    simp
  · have h_ge : j ≤ m.val := by omega
    have h_eq : m = Fin.natAdd j ⟨m.val - j, Nat.sub_lt_left_of_lt_add h_ge m.isLt⟩ := by
      ext; dsimp; omega
    rw [h_eq, osConcatPoint_natAdd, osConcatPoint_natAdd]

theorem osKernel_timeShift_symm {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    (𝒮 : SchwingerFamily ι) (htrans : OSTranslationInvariant 𝒮)
    (τ : ℝ) (hτ : 0 ≤ τ) (A B : OSConfig ι) :
    osKernel S 𝒮 (osConfigTimeShift τ hτ A) B =
      osKernel S 𝒮 A (osConfigTimeShift τ hτ B) := by
  rcases A with ⟨j, α, x, hx⟩
  rcases B with ⟨k, α', y, hy⟩
  dsimp [osKernel, osConfigTimeShift]
  refine Finset.sum_congr rfl (fun β _ => ?_)
  congr 1
  have h_ord : osConcatPoint j k (fun i => x i + euclidTimeVec τ) y ∈ orderedEuclidN (j + k) :=
    osConcatPoint_mem_orderedEuclidN j k (timeShift_mem_posOrderedEuclidN j hx hτ) hy
  rw [← htrans (j + k) (osConcatIdx j k β α')
    (osConcatPoint j k (fun i => x i + euclidTimeVec τ) y) h_ord (euclidTimeVec τ)]
  rw [osConcatPoint_timeShift_add]

def osTimeShiftLM {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (τ : ℝ) (hτ : 0 ≤ τ) :
    OSPreHilbertSpace D →ₗ[ℂ] OSPreHilbertSpace D :=
  osLiftConfigMap D (osConfigTimeShift τ hτ)

@[simp]
lemma osTimeShiftLM_zero {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) :
    osTimeShiftLM D 0 le_rfl = LinearMap.id := by
  dsimp [osTimeShiftLM]
  have h_id : osConfigTimeShift 0 le_rfl = (id : OSConfig ι → OSConfig ι) := by
    ext A
    exact osConfigTimeShift_zero A
  rw [h_id, osLiftConfigMap_id]

lemma osTimeShiftLM_add {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (τ₁ τ₂ : ℝ) (h₁ : 0 ≤ τ₁) (h₂ : 0 ≤ τ₂) :
    osTimeShiftLM D (τ₁ + τ₂) (add_nonneg h₁ h₂) =
      (osTimeShiftLM D τ₁ h₁).comp (osTimeShiftLM D τ₂ h₂) := by
  dsimp [osTimeShiftLM]
  have h_comp : osConfigTimeShift (τ₁ + τ₂) (add_nonneg h₁ h₂) =
      (osConfigTimeShift τ₁ h₁ : OSConfig ι → OSConfig ι) ∘ osConfigTimeShift τ₂ h₂ := by
    ext A
    exact osConfigTimeShift_add τ₁ τ₂ h₁ h₂ A
  rw [h_comp, osLiftConfigMap_comp]

@[simp]
lemma osTimeShiftLM_vacuumPre {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (τ : ℝ) (hτ : 0 ≤ τ) :
    osTimeShiftLM D τ hτ (osVacuumPre D) = osVacuumPre D := by
  dsimp [osTimeShiftLM, osVacuumPre]
  rw [osLiftConfigMap_osBasisPre, osConfigTimeShift_vacuum]

theorem osTimeShiftLM_isSymmetric {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (htrans : OSTranslationInvariant D.𝒮)
    (τ : ℝ) (hτ : 0 ≤ τ) :
    (osTimeShiftLM D τ hτ).IsSymmetric := by
  intro Ψ Φ
  unfold osTimeShiftLM
  have hL := inner_osLiftConfigMap D (osConfigTimeShift τ hτ) id Ψ Φ
  have hR := inner_osLiftConfigMap D id (osConfigTimeShift τ hτ) Ψ Φ
  rw [osLiftConfigMap_id, LinearMap.id_apply] at hL hR
  rw [hL, hR]
  refine Finsupp.sum_congr (fun A _ => Finsupp.sum_congr (fun B _ => ?_))
  rw [id_eq, id_eq, osKernel_timeShift_symm S D.𝒮 htrans τ hτ A B]

theorem inner_osTimeShiftLM_self_eq_norm_sq_half
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (htrans : OSTranslationInvariant D.𝒮)
    (τ : ℝ) (hτ : 0 ≤ τ) (Ψ : OSPreHilbertSpace D) :
    ⟪osTimeShiftLM D τ hτ Ψ, Ψ⟫_ℂ = (‖osTimeShiftLM D (τ / 2) (by linarith) Ψ‖ ^ 2 : ℂ) := by
  have h_half : 0 ≤ τ / 2 := by linarith
  have h_eq : osTimeShiftLM D τ hτ Ψ =
      osTimeShiftLM D (τ / 2) h_half (osTimeShiftLM D (τ / 2) h_half Ψ) := by
    rw [← LinearMap.comp_apply, ← osTimeShiftLM_add D (τ / 2) (τ / 2) h_half h_half]
    congr 2
    ring
  rw [h_eq, osTimeShiftLM_isSymmetric D htrans (τ / 2) h_half]
  exact inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (osTimeShiftLM D (τ / 2) h_half Ψ)

theorem osTimeShiftLM_re_inner_nonneg {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (htrans : OSTranslationInvariant D.𝒮)
    (τ : ℝ) (hτ : 0 ≤ τ) (Ψ : OSPreHilbertSpace D) :
    0 ≤ RCLike.re ⟪osTimeShiftLM D τ hτ Ψ, Ψ⟫_ℂ := by
  rw [inner_osTimeShiftLM_self_eq_norm_sq_half D htrans τ hτ Ψ]
  have h_re : RCLike.re (‖osTimeShiftLM D (τ / 2) (by linarith) Ψ‖ ^ 2 : ℂ) =
      ‖osTimeShiftLM D (τ / 2) (by linarith) Ψ‖ ^ 2 := by
    norm_cast
  rw [h_re]
  exact sq_nonneg _

theorem norm_sq_osTimeShiftLM_le {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (htrans : OSTranslationInvariant D.𝒮)
    (τ : ℝ) (hτ : 0 ≤ τ) (Ψ : OSPreHilbertSpace D) :
    ‖osTimeShiftLM D τ hτ Ψ‖ ^ 2 ≤
      ‖Ψ‖ * ‖osTimeShiftLM D (2 * τ) (by linarith) Ψ‖ := by
  have h2τ : 0 ≤ 2 * τ := by linarith
  have h_id : ‖osTimeShiftLM D τ hτ Ψ‖ ^ 2 =
      RCLike.re ⟪Ψ, osTimeShiftLM D (2 * τ) h2τ Ψ⟫_ℂ := by
    rw [← osTimeShiftLM_isSymmetric D htrans (2 * τ) h2τ Ψ Ψ]
    rw [inner_osTimeShiftLM_self_eq_norm_sq_half D htrans (2 * τ) h2τ Ψ]
    have h_eq : osTimeShiftLM D (2 * τ / 2) (by linarith) Ψ = osTimeShiftLM D τ hτ Ψ := by
      congr 2
      ring
    rw [h_eq]
    norm_cast
  rw [h_id]
  calc RCLike.re ⟪Ψ, osTimeShiftLM D (2 * τ) h2τ Ψ⟫_ℂ
    _ ≤ ‖⟪Ψ, osTimeShiftLM D (2 * τ) h2τ Ψ⟫_ℂ‖ := RCLike.re_le_norm _
    _ ≤ ‖Ψ‖ * ‖osTimeShiftLM D (2 * τ) h2τ Ψ‖ := norm_inner_le_norm _ _

theorem norm_pow_two_pow_osTimeShiftLM_le {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (htrans : OSTranslationInvariant D.𝒮)
    (m : ℕ) (τ : ℝ) (hτ : 0 ≤ τ) (Ψ : OSPreHilbertSpace D) :
    ‖osTimeShiftLM D τ hτ Ψ‖ ^ (2 ^ m) ≤
      ‖Ψ‖ ^ (2 ^ m - 1) *
        ‖osTimeShiftLM D ((2 : ℝ) ^ m * τ) (mul_nonneg (by positivity) hτ) Ψ‖ := by
  induction m generalizing τ with
  | zero =>
    simp
  | succ m ih =>
    have h2τ : 0 ≤ 2 * τ := by linarith
    have h_step := norm_sq_osTimeShiftLM_le D htrans τ hτ Ψ
    have h_pow : (‖osTimeShiftLM D τ hτ Ψ‖ ^ 2) ^ (2 ^ m) ≤
        (‖Ψ‖ * ‖osTimeShiftLM D (2 * τ) h2τ Ψ‖) ^ (2 ^ m) :=
      pow_le_pow_left₀ (by positivity) h_step (2 ^ m)
    rw [← pow_mul, mul_comm 2 (2 ^ m), ← pow_succ, mul_pow] at h_pow
    have h_ih := ih (2 * τ) h2τ
    have h_mul := mul_le_mul_of_nonneg_left h_ih (pow_nonneg (norm_nonneg Ψ) (2 ^ m))
    refine le_trans h_pow (le_trans h_mul ?_)
    rw [← mul_assoc, ← pow_add]
    have h_exp : 2 ^ m + (2 ^ m - 1) = 2 ^ (m + 1) - 1 := by
      have h_pos : 1 ≤ 2 ^ m := Nat.one_le_two_pow
      omega
    rw [h_exp]
    have h_time : osTimeShiftLM D ((2 : ℝ) ^ m * (2 * τ)) (mul_nonneg (by positivity) h2τ) Ψ =
        osTimeShiftLM D ((2 : ℝ) ^ (m + 1) * τ) (mul_nonneg (by positivity) hτ) Ψ := by
      congr 2
      ring
    rw [h_time]

def OSContractionCondition {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) : Prop :=
  ∀ (τ : ℝ) (hτ : 0 ≤ τ) (Ψ : OSPreHilbertSpace D),
    ‖osTimeShiftLM D τ hτ Ψ‖ ≤ ‖Ψ‖

def osTimeShiftPreCLM {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (hcontr : OSContractionCondition D)
    (τ : ℝ) (hτ : 0 ≤ τ) :
    OSPreHilbertSpace D →L[ℂ] OSPreHilbertSpace D :=
  (osTimeShiftLM D τ hτ).mkContinuous 1 (fun Ψ => by simpa using hcontr τ hτ Ψ)

@[simp]
lemma osTimeShiftPreCLM_apply {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (hcontr : OSContractionCondition D)
    (τ : ℝ) (hτ : 0 ≤ τ) (Ψ : OSPreHilbertSpace D) :
    osTimeShiftPreCLM D hcontr τ hτ Ψ = osTimeShiftLM D τ hτ Ψ := rfl

def osContractionSemigroup {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (hcontr : OSContractionCondition D)
    (τ : ℝ) (hτ : 0 ≤ τ) :
    OSHilbert D →L[ℂ] OSHilbert D :=
  (osTimeShiftPreCLM D hcontr τ hτ).completion

@[simp]
lemma osContractionSemigroup_toOSHilbert {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (hcontr : OSContractionCondition D)
    (τ : ℝ) (hτ : 0 ≤ τ) (Ψ : OSPreHilbertSpace D) :
    osContractionSemigroup D hcontr τ hτ (toOSHilbert D Ψ) =
      toOSHilbert D (osTimeShiftLM D τ hτ Ψ) :=
  ContinuousLinearMap.completion_apply_coe (osTimeShiftPreCLM D hcontr τ hτ) Ψ

@[simp]
theorem osContractionSemigroup_zero {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (hcontr : OSContractionCondition D) :
    osContractionSemigroup D hcontr 0 le_rfl = ContinuousLinearMap.id ℂ (OSHilbert D) := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih Ψ =>
    change osContractionSemigroup D hcontr 0 le_rfl (toOSHilbert D Ψ) = toOSHilbert D Ψ
    rw [osContractionSemigroup_toOSHilbert, osTimeShiftLM_zero, LinearMap.id_apply]

theorem osContractionSemigroup_add {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (hcontr : OSContractionCondition D)
    (τ₁ τ₂ : ℝ) (h₁ : 0 ≤ τ₁) (h₂ : 0 ≤ τ₂) :
    osContractionSemigroup D hcontr (τ₁ + τ₂) (add_nonneg h₁ h₂) =
      (osContractionSemigroup D hcontr τ₁ h₁).comp (osContractionSemigroup D hcontr τ₂ h₂) := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih Ψ =>
    change osContractionSemigroup D hcontr (τ₁ + τ₂) (add_nonneg h₁ h₂) (toOSHilbert D Ψ) =
      osContractionSemigroup D hcontr τ₁ h₁
        (osContractionSemigroup D hcontr τ₂ h₂ (toOSHilbert D Ψ))
    rw [osContractionSemigroup_toOSHilbert, osContractionSemigroup_toOSHilbert,
        osContractionSemigroup_toOSHilbert, osTimeShiftLM_add, LinearMap.comp_apply]

@[simp]
theorem osContractionSemigroup_vacuum {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (hcontr : OSContractionCondition D)
    (τ : ℝ) (hτ : 0 ≤ τ) :
    osContractionSemigroup D hcontr τ hτ (osVacuum D) = osVacuum D := by
  dsimp [osVacuum]
  rw [osContractionSemigroup_toOSHilbert, osTimeShiftLM_vacuumPre]

theorem norm_osContractionSemigroup_le {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (hcontr : OSContractionCondition D)
    (τ : ℝ) (hτ : 0 ≤ τ) (x : OSHilbert D) :
    ‖osContractionSemigroup D hcontr τ hτ x‖ ≤ ‖x‖ := by
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_le (by fun_prop) (by fun_prop)
  | ih Ψ =>
    change ‖osContractionSemigroup D hcontr τ hτ (toOSHilbert D Ψ)‖ ≤ ‖toOSHilbert D Ψ‖
    rw [osContractionSemigroup_toOSHilbert, norm_toOSHilbert, norm_toOSHilbert]
    exact hcontr τ hτ Ψ

theorem opNorm_osContractionSemigroup_le_one {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (hcontr : OSContractionCondition D)
    (τ : ℝ) (hτ : 0 ≤ τ) :
    ‖osContractionSemigroup D hcontr τ hτ‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by
    simpa using norm_osContractionSemigroup_le D hcontr τ hτ x)

theorem osContractionSemigroup_isSymmetric {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (htrans : OSTranslationInvariant D.𝒮)
    (hcontr : OSContractionCondition D) (τ : ℝ) (hτ : 0 ≤ τ) :
    (osContractionSemigroup D hcontr τ hτ : OSHilbert D →ₗ[ℂ] OSHilbert D).IsSymmetric := by
  intro x y
  induction x, y using UniformSpace.Completion.induction_on₂ with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih Ψ Φ =>
    change ⟪osContractionSemigroup D hcontr τ hτ (toOSHilbert D Ψ), toOSHilbert D Φ⟫_ℂ =
      ⟪toOSHilbert D Ψ, osContractionSemigroup D hcontr τ hτ (toOSHilbert D Φ)⟫_ℂ
    rw [osContractionSemigroup_toOSHilbert, osContractionSemigroup_toOSHilbert,
        inner_toOSHilbert, inner_toOSHilbert]
    exact osTimeShiftLM_isSymmetric D htrans τ hτ Ψ Φ

theorem osContractionSemigroup_isPositive {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (htrans : OSTranslationInvariant D.𝒮)
    (hcontr : OSContractionCondition D) (τ : ℝ) (hτ : 0 ≤ τ) :
    (osContractionSemigroup D hcontr τ hτ : OSHilbert D →ₗ[ℂ] OSHilbert D).IsPositive := by
  refine ⟨osContractionSemigroup_isSymmetric D htrans hcontr τ hτ, fun x => ?_⟩
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_le (by fun_prop) (by fun_prop)
  | ih Ψ =>
    change 0 ≤ RCLike.re ⟪osContractionSemigroup D hcontr τ hτ (toOSHilbert D Ψ), toOSHilbert D Ψ⟫_ℂ
    rw [osContractionSemigroup_toOSHilbert, inner_toOSHilbert]
    exact osTimeShiftLM_re_inner_nonneg D htrans τ hτ Ψ

def euclidSpatialVec (a : Fin 3 → ℝ) : Fin 4 → ℝ :=
  Fin.cons 0 a

@[simp]
lemma euclidSpatialVec_zero_apply (a : Fin 3 → ℝ) :
    euclidSpatialVec a 0 = 0 := rfl

@[simp]
lemma euclidSpatialVec_zero : euclidSpatialVec 0 = 0 := by
  ext μ
  fin_cases μ <;> rfl

lemma euclidSpatialVec_add (a b : Fin 3 → ℝ) :
    euclidSpatialVec (a + b) = euclidSpatialVec a + euclidSpatialVec b := by
  ext μ
  refine Fin.cases ?_ ?_ μ
  · simp [euclidSpatialVec]
  · intro i
    simp [euclidSpatialVec]

@[simp]
lemma euclidTimeReflect_euclidSpatialVec_eq (a : Fin 3 → ℝ) :
    euclidTimeReflect (euclidSpatialVec a) = euclidSpatialVec a := by
  ext μ
  fin_cases μ <;> simp [euclidTimeReflect, euclidSpatialVec]

lemma spatialShift_mem_posOrderedEuclidN (n : ℕ) {x : Fin n → Fin 4 → ℝ}
    (hx : x ∈ posOrderedEuclidN n) (a : Fin 3 → ℝ) :
    (fun i => x i + euclidSpatialVec a) ∈ posOrderedEuclidN n := by
  refine ⟨fun i => ?_, shift_mem_orderedEuclidN n hx.2 (euclidSpatialVec a)⟩
  simp only [Pi.add_apply, euclidSpatialVec_zero_apply, add_zero]
  exact hx.1 i

def osConfigSpatialShift (a : Fin 3 → ℝ) (A : OSConfig ι) : OSConfig ι :=
  ⟨A.1, (A.2.1, ⟨fun i => A.2.2.val i + euclidSpatialVec a,
    spatialShift_mem_posOrderedEuclidN A.1 A.2.2.property a⟩)⟩

lemma osConcatPoint_spatialShift (j k : ℕ) (x : Fin j → Fin 4 → ℝ) (y : Fin k → Fin 4 → ℝ)
    (a : Fin 3 → ℝ) :
    osConcatPoint j k (fun i => x i + euclidSpatialVec a) (fun i => y i + euclidSpatialVec a) =
      fun m => osConcatPoint j k x y m + euclidSpatialVec a := by
  ext m μ
  by_cases hm : m.val < j
  · have h_eq : m = Fin.castAdd k ⟨m.val, hm⟩ := by ext; rfl
    rw [h_eq, osConcatPoint_castAdd, Pi.add_apply, osConcatPoint_castAdd]
    rw [euclidTimeReflect_add, euclidTimeReflect_euclidSpatialVec_eq]
    rfl
  · have h_ge : j ≤ m.val := by omega
    have h_eq : m = Fin.natAdd j ⟨m.val - j, Nat.sub_lt_left_of_lt_add h_ge m.isLt⟩ := by
      ext; dsimp; omega
    rw [h_eq, osConcatPoint_natAdd, Pi.add_apply, osConcatPoint_natAdd]
    rfl

theorem osKernel_spatialShift_invariant {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    (𝒮 : SchwingerFamily ι) (htrans : OSTranslationInvariant 𝒮)
    (a : Fin 3 → ℝ) (A B : OSConfig ι) :
    osKernel S 𝒮 (osConfigSpatialShift a A) (osConfigSpatialShift a B) =
      osKernel S 𝒮 A B := by
  rcases A with ⟨j, α, x, hx⟩
  rcases B with ⟨k, α', y, hy⟩
  dsimp [osKernel, osConfigSpatialShift]
  refine Finset.sum_congr rfl (fun β _ => ?_)
  congr 1
  rw [osConcatPoint_spatialShift]
  exact htrans (j + k) (osConcatIdx j k β α') (osConcatPoint j k x y)
    (osConcatPoint_mem_orderedEuclidN j k hx hy) (euclidSpatialVec a)

def osSpatialTranslateLM {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (a : Fin 3 → ℝ) :
    OSPreHilbertSpace D →ₗ[ℂ] OSPreHilbertSpace D :=
  osLiftConfigMap D (osConfigSpatialShift a)

theorem inner_osSpatialTranslateLM {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (htrans : OSTranslationInvariant D.𝒮)
    (a : Fin 3 → ℝ) (Ψ Φ : OSPreHilbertSpace D) :
    ⟪osSpatialTranslateLM D a Ψ, osSpatialTranslateLM D a Φ⟫_ℂ = ⟪Ψ, Φ⟫_ℂ := by
  unfold osSpatialTranslateLM
  rw [inner_osLiftConfigMap D (osConfigSpatialShift a) (osConfigSpatialShift a) Ψ Φ,
      OSPreHilbertSpace.inner_def]
  unfold osPreInner
  refine Finsupp.sum_congr (fun A _ => Finsupp.sum_congr (fun B _ => ?_))
  rw [osKernel_spatialShift_invariant S D.𝒮 htrans a A B]

theorem norm_osSpatialTranslateLM {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (htrans : OSTranslationInvariant D.𝒮)
    (a : Fin 3 → ℝ) (Ψ : OSPreHilbertSpace D) :
    ‖osSpatialTranslateLM D a Ψ‖ = ‖Ψ‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ),
      inner_osSpatialTranslateLM D htrans a Ψ Ψ]

def osSpatialTranslatePreCLM {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (htrans : OSTranslationInvariant D.𝒮)
    (a : Fin 3 → ℝ) :
    OSPreHilbertSpace D →L[ℂ] OSPreHilbertSpace D :=
  (osSpatialTranslateLM D a).mkContinuous 1 (fun Ψ => by
    rw [one_mul, norm_osSpatialTranslateLM D htrans a Ψ])

def osSpatialTranslate {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (htrans : OSTranslationInvariant D.𝒮)
    (a : Fin 3 → ℝ) :
    OSHilbert D →L[ℂ] OSHilbert D :=
  (osSpatialTranslatePreCLM D htrans a).completion

@[simp]
lemma osSpatialTranslate_toOSHilbert {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (htrans : OSTranslationInvariant D.𝒮)
    (a : Fin 3 → ℝ) (Ψ : OSPreHilbertSpace D) :
    osSpatialTranslate D htrans a (toOSHilbert D Ψ) =
      toOSHilbert D (osSpatialTranslateLM D a Ψ) :=
  ContinuousLinearMap.completion_apply_coe (osSpatialTranslatePreCLM D htrans a) Ψ

theorem inner_osSpatialTranslate {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (htrans : OSTranslationInvariant D.𝒮)
    (a : Fin 3 → ℝ) (x y : OSHilbert D) :
    ⟪osSpatialTranslate D htrans a x, osSpatialTranslate D htrans a y⟫_ℂ = ⟪x, y⟫_ℂ := by
  induction x, y using UniformSpace.Completion.induction_on₂ with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih Ψ Φ =>
    change ⟪osSpatialTranslate D htrans a (toOSHilbert D Ψ),
        osSpatialTranslate D htrans a (toOSHilbert D Φ)⟫_ℂ =
      ⟪toOSHilbert D Ψ, toOSHilbert D Φ⟫_ℂ
    rw [osSpatialTranslate_toOSHilbert, osSpatialTranslate_toOSHilbert,
        inner_toOSHilbert, inner_toOSHilbert, inner_osSpatialTranslateLM D htrans a Ψ Φ]

omit [Fintype ι] [DecidableEq ι] in
lemma osConfigSpatialShift_comm_osConfigTimeShift
    (a : Fin 3 → ℝ) (τ : ℝ) (hτ : 0 ≤ τ) :
    osConfigSpatialShift (ι := ι) a ∘ osConfigTimeShift τ hτ =
      osConfigTimeShift τ hτ ∘ osConfigSpatialShift a := by
  ext A : 1
  rcases A with ⟨m, α, ⟨y, hy⟩⟩
  dsimp [osConfigSpatialShift, osConfigTimeShift]
  congr 2
  ext i μ
  simp only [Pi.add_apply]
  ring

theorem osSpatialTranslate_comm_osContractionSemigroup
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (htrans : OSTranslationInvariant D.𝒮)
    (hcontr : OSContractionCondition D) (a : Fin 3 → ℝ) (τ : ℝ) (hτ : 0 ≤ τ) :
    (osSpatialTranslate D htrans a).comp (osContractionSemigroup D hcontr τ hτ) =
      (osContractionSemigroup D hcontr τ hτ).comp (osSpatialTranslate D htrans a) := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih Ψ =>
    change osSpatialTranslate D htrans a (osContractionSemigroup D hcontr τ hτ (toOSHilbert D Ψ)) =
      osContractionSemigroup D hcontr τ hτ (osSpatialTranslate D htrans a (toOSHilbert D Ψ))
    rw [osContractionSemigroup_toOSHilbert, osSpatialTranslate_toOSHilbert,
        osSpatialTranslate_toOSHilbert, osContractionSemigroup_toOSHilbert]
    congr 1
    dsimp [osSpatialTranslateLM, osTimeShiftLM]
    rw [← LinearMap.comp_apply, ← LinearMap.comp_apply,
        ← osLiftConfigMap_comp, ← osLiftConfigMap_comp,
        osConfigSpatialShift_comm_osConfigTimeShift]

def su2Conj (U : SU2) : SU2 :=
  ⟨(U⁻¹).valᵀ, by
    have hUinv := Matrix.mem_specialUnitaryGroup_iff.mp (U⁻¹).property
    have h_unit' : (U⁻¹).valᴴ * (U⁻¹).val = 1 :=
      Matrix.mem_unitaryGroup_iff'.mp hUinv.1
    rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
    refine ⟨?_, by rw [Matrix.det_transpose, hUinv.2]⟩
    change (U⁻¹).valᵀ * ((U⁻¹).valᵀ)ᴴ = 1
    have h_ct : ((U⁻¹).valᵀ)ᴴ = ((U⁻¹).valᴴ)ᵀ := (Matrix.conjTranspose_transpose (U⁻¹).val).symm
    rw [h_ct, ← Matrix.transpose_mul, h_unit', Matrix.transpose_one]⟩

@[simp]
lemma su2Conj_val_transpose (U : SU2) :
    (su2Conj U).valᵀ = (U⁻¹).val :=
  Matrix.transpose_transpose (U⁻¹).val

lemma vec_to_spinor_wickEmbed_euclidTimeVec (τ : ℝ) :
    vec_to_spinor (wickEmbed (euclidTimeVec τ)) =
      (Complex.I * (τ : ℂ)) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [vec_to_spinor, wickEmbed, euclidTimeVec, mul_comm]

theorem euclidRotApply_su2Conj_euclidTimeVec (U : SU2) (τ : ℝ) :
    euclidRotApply U (su2Conj U) (euclidTimeVec τ) = euclidTimeVec τ := by
  apply wickEmbed_injective
  rw [wickEmbed_euclidRotApply]
  have h_act : vec_to_spinor (spinorPhi (su2ToSL2C U, su2ToSL2C (su2Conj U)) •
      wickEmbed (euclidTimeVec τ)) =
      U.val * vec_to_spinor (wickEmbed (euclidTimeVec τ)) * (su2Conj U).valᵀ := by
    change vec_to_spinor (spinorPhi_matrix (su2ToSL2C U) (su2ToSL2C (su2Conj U)) *ᵥ
      wickEmbed (euclidTimeVec τ)) = _
    rw [spinorPhi_matrix_mulVec]
    simp [spinor_action, vec_to_spinor_right_inv, su2ToSL2C]
  have h_eq : vec_to_spinor (spinorPhi (su2ToSL2C U, su2ToSL2C (su2Conj U)) •
      wickEmbed (euclidTimeVec τ)) = vec_to_spinor (wickEmbed (euclidTimeVec τ)) := by
    rw [h_act, su2Conj_val_transpose, vec_to_spinor_wickEmbed_euclidTimeVec]
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
    have hU : U.val * (U⁻¹).val = 1 := by
      change (U * U⁻¹).val = 1
      rw [mul_inv_cancel]
      rfl
    rw [hU]
  simpa only [spinor_to_vec_left_inv] using congrArg spinor_to_vec h_eq

@[simp]
theorem euclidRotApply_su2Conj_time (U : SU2) (x : Fin 4 → ℝ) :
    euclidRotApply U (su2Conj U) x 0 = x 0 := by
  have h1 : euclidRotApply U (su2Conj U) x 0 =
      euclidInner (euclidRotApply U (su2Conj U) x) (euclidTimeVec 1) := by
    rw [euclidInner_euclidTimeVec_right, mul_one]
  rw [h1]
  conv_lhs => rw [← euclidRotApply_su2Conj_euclidTimeVec U 1]
  rw [euclidInner_euclidRotApply, euclidInner_euclidTimeVec_right, mul_one]

theorem euclidTimeReflect_euclidRotApply_su2Conj (U : SU2) (x : Fin 4 → ℝ) :
    euclidTimeReflect (euclidRotApply U (su2Conj U) x) =
      euclidRotApply U (su2Conj U) (euclidTimeReflect x) := by
  have h_decomp : ∀ y : Fin 4 → ℝ,
      euclidTimeReflect y = y + (-2 * y 0) • euclidTimeVec 1 := by
    intro y
    ext μ
    fin_cases μ <;> · simp [euclidTimeReflect, euclidTimeVec]; try ring
  rw [h_decomp, h_decomp, euclidRotApply_add, euclidRotApply_smul,
      euclidRotApply_su2Conj_euclidTimeVec, euclidRotApply_su2Conj_time]

theorem euclidRotN_su2Conj_mem_posOrderedEuclidN (n : ℕ) (U : SU2)
    {x : Fin n → Fin 4 → ℝ} (hx : x ∈ posOrderedEuclidN n) :
    euclidRotN n U (su2Conj U) x ∈ posOrderedEuclidN n := by
  refine ⟨fun i => ?_, fun i hi => ?_⟩
  · dsimp [euclidRotN]
    rw [euclidRotOfSU2_mulVec, euclidRotApply_su2Conj_time]
    exact hx.1 i
  · dsimp [euclidRotN]
    rw [euclidRotOfSU2_mulVec, euclidRotOfSU2_mulVec,
        euclidRotApply_su2Conj_time, euclidRotApply_su2Conj_time]
    exact hx.2 i hi

def osConfigPointRot (U : SU2) (A : OSConfig ι) : OSConfig ι :=
  ⟨A.1, (A.2.1, ⟨euclidRotN A.1 U (su2Conj U) A.2.2.val,
    euclidRotN_su2Conj_mem_posOrderedEuclidN A.1 U A.2.2.property⟩)⟩

lemma osConcatPoint_euclidRotN_su2Conj (j k : ℕ) (U : SU2)
    (x : Fin j → Fin 4 → ℝ) (y : Fin k → Fin 4 → ℝ) :
    osConcatPoint j k (euclidRotN j U (su2Conj U) x) (euclidRotN k U (su2Conj U) y) =
      euclidRotN (j + k) U (su2Conj U) (osConcatPoint j k x y) := by
  ext m μ
  by_cases hm : m.val < j
  · have h_eq : m = Fin.castAdd k ⟨m.val, hm⟩ := by ext; rfl
    rw [h_eq, osConcatPoint_castAdd]
    change euclidTimeReflect (euclidRotOfSU2 U (su2Conj U) *ᵥ x (Fin.rev ⟨m.val, hm⟩)) μ =
      (euclidRotOfSU2 U (su2Conj U) *ᵥ osConcatPoint j k x y (Fin.castAdd k ⟨m.val, hm⟩)) μ
    rw [osConcatPoint_castAdd, euclidRotOfSU2_mulVec, euclidRotOfSU2_mulVec,
        euclidTimeReflect_euclidRotApply_su2Conj]
  · have h_ge : j ≤ m.val := by omega
    have h_eq : m = Fin.natAdd j ⟨m.val - j, Nat.sub_lt_left_of_lt_add h_ge m.isLt⟩ := by
      ext; dsimp; omega
    rw [h_eq, osConcatPoint_natAdd]
    change (euclidRotOfSU2 U (su2Conj U) *ᵥ y ⟨m.val - j, _⟩) μ =
      (euclidRotOfSU2 U (su2Conj U) *ᵥ osConcatPoint j k x y (Fin.natAdd j ⟨m.val - j, _⟩)) μ
    rw [osConcatPoint_natAdd]

def OSScalarRotInvariant (𝒮 : SchwingerFamily ι) : Prop :=
  ∀ (n : ℕ) (U : SU2) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
    x ∈ orderedEuclidN n →
    𝒮 n α (euclidRotN n U (su2Conj U) x) = 𝒮 n α x

theorem osKernel_pointRot_invariant {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    (𝒮 : SchwingerFamily ι) (hrot : OSScalarRotInvariant 𝒮)
    (U : SU2) (A B : OSConfig ι) :
    osKernel S 𝒮 (osConfigPointRot U A) (osConfigPointRot U B) =
      osKernel S 𝒮 A B := by
  rcases A with ⟨j, α, x, hx⟩
  rcases B with ⟨k, α', y, hy⟩
  dsimp [osKernel, osConfigPointRot]
  refine Finset.sum_congr rfl (fun β _ => ?_)
  congr 1
  rw [osConcatPoint_euclidRotN_su2Conj]
  exact hrot (j + k) U (osConcatIdx j k β α') (osConcatPoint j k x y)
    (osConcatPoint_mem_orderedEuclidN j k hx hy)

def osSpatialRotLM {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (U : SU2) :
    OSPreHilbertSpace D →ₗ[ℂ] OSPreHilbertSpace D :=
  osLiftConfigMap D (osConfigPointRot U)

theorem inner_osSpatialRotLM {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (hrot : OSScalarRotInvariant D.𝒮)
    (U : SU2) (Ψ Φ : OSPreHilbertSpace D) :
    ⟪osSpatialRotLM D U Ψ, osSpatialRotLM D U Φ⟫_ℂ = ⟪Ψ, Φ⟫_ℂ := by
  unfold osSpatialRotLM
  rw [inner_osLiftConfigMap D (osConfigPointRot U) (osConfigPointRot U) Ψ Φ,
      OSPreHilbertSpace.inner_def]
  unfold osPreInner
  refine Finsupp.sum_congr (fun A _ => Finsupp.sum_congr (fun B _ => ?_))
  rw [osKernel_pointRot_invariant S D.𝒮 hrot U A B]

theorem norm_osSpatialRotLM {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (hrot : OSScalarRotInvariant D.𝒮)
    (U : SU2) (Ψ : OSPreHilbertSpace D) :
    ‖osSpatialRotLM D U Ψ‖ = ‖Ψ‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ),
      inner_osSpatialRotLM D hrot U Ψ Ψ]

def osSpatialRotPreCLM {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (hrot : OSScalarRotInvariant D.𝒮) (U : SU2) :
    OSPreHilbertSpace D →L[ℂ] OSPreHilbertSpace D :=
  (osSpatialRotLM D U).mkContinuous 1 (fun Ψ => by
    rw [one_mul, norm_osSpatialRotLM D hrot U Ψ])

def osSpatialRot {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (hrot : OSScalarRotInvariant D.𝒮) (U : SU2) :
    OSHilbert D →L[ℂ] OSHilbert D :=
  (osSpatialRotPreCLM D hrot U).completion

@[simp]
lemma osSpatialRot_toOSHilbert {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (hrot : OSScalarRotInvariant D.𝒮)
    (U : SU2) (Ψ : OSPreHilbertSpace D) :
    osSpatialRot D hrot U (toOSHilbert D Ψ) =
      toOSHilbert D (osSpatialRotLM D U Ψ) :=
  ContinuousLinearMap.completion_apply_coe (osSpatialRotPreCLM D hrot U) Ψ

theorem inner_osSpatialRot {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (hrot : OSScalarRotInvariant D.𝒮)
    (U : SU2) (x y : OSHilbert D) :
    ⟪osSpatialRot D hrot U x, osSpatialRot D hrot U y⟫_ℂ = ⟪x, y⟫_ℂ := by
  induction x, y using UniformSpace.Completion.induction_on₂ with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih Ψ Φ =>
    change ⟪osSpatialRot D hrot U (toOSHilbert D Ψ),
        osSpatialRot D hrot U (toOSHilbert D Φ)⟫_ℂ =
      ⟪toOSHilbert D Ψ, toOSHilbert D Φ⟫_ℂ
    rw [osSpatialRot_toOSHilbert, osSpatialRot_toOSHilbert,
        inner_toOSHilbert, inner_toOSHilbert, inner_osSpatialRotLM D hrot U Ψ Φ]

omit [Fintype ι] [DecidableEq ι] in
lemma osConfigPointRot_comm_osConfigTimeShift
    (U : SU2) (τ : ℝ) (hτ : 0 ≤ τ) :
    osConfigPointRot (ι := ι) U ∘ osConfigTimeShift τ hτ =
      osConfigTimeShift τ hτ ∘ osConfigPointRot U := by
  ext A : 1
  rcases A with ⟨m, α, ⟨y, hy⟩⟩
  dsimp [osConfigPointRot, osConfigTimeShift]
  congr 2
  ext i μ
  dsimp [euclidRotN]
  rw [euclidRotOfSU2_mulVec, euclidRotApply_add, euclidRotApply_su2Conj_euclidTimeVec,
      ← euclidRotOfSU2_mulVec]
  rfl

theorem osSpatialRot_comm_osContractionSemigroup
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (hrot : OSScalarRotInvariant D.𝒮)
    (hcontr : OSContractionCondition D) (U : SU2) (τ : ℝ) (hτ : 0 ≤ τ) :
    (osSpatialRot D hrot U).comp (osContractionSemigroup D hcontr τ hτ) =
      (osContractionSemigroup D hcontr τ hτ).comp (osSpatialRot D hrot U) := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih Ψ =>
    change osSpatialRot D hrot U (osContractionSemigroup D hcontr τ hτ (toOSHilbert D Ψ)) =
      osContractionSemigroup D hcontr τ hτ (osSpatialRot D hrot U (toOSHilbert D Ψ))
    rw [osContractionSemigroup_toOSHilbert, osSpatialRot_toOSHilbert,
        osSpatialRot_toOSHilbert, osContractionSemigroup_toOSHilbert]
    congr 1
    dsimp [osSpatialRotLM, osTimeShiftLM]
    rw [← LinearMap.comp_apply, ← LinearMap.comp_apply,
        ← osLiftConfigMap_comp, ← osLiftConfigMap_comp,
        osConfigPointRot_comm_osConfigTimeShift]

def rightHalfPlane : Set ℂ := {z : ℂ | 0 ≤ z.re}

def openRightHalfPlane : Set ℂ := {z : ℂ | 0 < z.re}

lemma zero_mem_rightHalfPlane : (0 : ℂ) ∈ rightHalfPlane := by
  simp [rightHalfPlane]

lemma add_mem_rightHalfPlane {z₁ z₂ : ℂ}
    (h₁ : z₁ ∈ rightHalfPlane) (h₂ : z₂ ∈ rightHalfPlane) :
    z₁ + z₂ ∈ rightHalfPlane := by
  simp only [rightHalfPlane, Set.mem_setOf_eq, Complex.add_re] at h₁ h₂ ⊢
  linarith

lemma ofReal_mem_rightHalfPlane {τ : ℝ} (hτ : 0 ≤ τ) :
    (τ : ℂ) ∈ rightHalfPlane := by
  simpa [rightHalfPlane] using hτ

lemma star_mem_rightHalfPlane {z : ℂ} (hz : z ∈ rightHalfPlane) :
    star z ∈ rightHalfPlane := by
  simpa [rightHalfPlane] using hz

lemma mul_I_mem_rightHalfPlane (t : ℝ) :
    Complex.I * (t : ℂ) ∈ rightHalfPlane := by
  simp [rightHalfPlane]

lemma add_mul_I_mem_rightHalfPlane {τ : ℝ} (hτ : 0 ≤ τ) (t : ℝ) :
    (τ : ℂ) + Complex.I * (t : ℂ) ∈ rightHalfPlane :=
  add_mem_rightHalfPlane (ofReal_mem_rightHalfPlane hτ) (mul_I_mem_rightHalfPlane t)

structure OSHolomorphicSemigroup {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (hcontr : OSContractionCondition D) where
  Z : ∀ z : ℂ, z ∈ rightHalfPlane → (OSHilbert D →L[ℂ] OSHilbert D)
  real_eq : ∀ (τ : ℝ) (hτ : 0 ≤ τ),
    Z (τ : ℂ) (ofReal_mem_rightHalfPlane hτ) = osContractionSemigroup D hcontr τ hτ
  map_add : ∀ (z₁ z₂ : ℂ) (h₁ : z₁ ∈ rightHalfPlane) (h₂ : z₂ ∈ rightHalfPlane),
    Z (z₁ + z₂) (add_mem_rightHalfPlane h₁ h₂) = (Z z₁ h₁).comp (Z z₂ h₂)
  vacuum : ∀ (z : ℂ) (hz : z ∈ rightHalfPlane),
    Z z hz (osVacuum D) = osVacuum D
  contraction : ∀ (z : ℂ) (hz : z ∈ rightHalfPlane) (x : OSHilbert D),
    ‖Z z hz x‖ ≤ ‖x‖
  adjoint_symm : ∀ (z : ℂ) (hz : z ∈ rightHalfPlane) (x y : OSHilbert D),
    ⟪Z z hz x, y⟫_ℂ = ⟪x, Z (star z) (star_mem_rightHalfPlane hz) y⟫_ℂ
  comm_spatial : ∀ (htrans : OSTranslationInvariant D.𝒮) (a : Fin 3 → ℝ)
    (z : ℂ) (hz : z ∈ rightHalfPlane),
    (osSpatialTranslate D htrans a).comp (Z z hz) =
      (Z z hz).comp (osSpatialTranslate D htrans a)

namespace OSHolomorphicSemigroup

variable {R : HolomorphicLorentzRep ι} {S : StarStructure R}
  {D : OSReflectionPositiveData R S} {hcontr : OSContractionCondition D}

@[simp]
theorem map_zero (ℰ : OSHolomorphicSemigroup D hcontr) :
    ℰ.Z 0 zero_mem_rightHalfPlane = ContinuousLinearMap.id ℂ (OSHilbert D) := by
  have h := ℰ.real_eq 0 le_rfl
  simpa using h.trans (osContractionSemigroup_zero D hcontr)

theorem opNorm_le_one (ℰ : OSHolomorphicSemigroup D hcontr)
    (z : ℂ) (hz : z ∈ rightHalfPlane) :
    ‖ℰ.Z z hz‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by
    simpa using ℰ.contraction z hz x)

theorem decomp_real_imag (ℰ : OSHolomorphicSemigroup D hcontr)
    (τ : ℝ) (hτ : 0 ≤ τ) (t : ℝ) :
    ℰ.Z ((τ : ℂ) + Complex.I * (t : ℂ)) (add_mul_I_mem_rightHalfPlane hτ t) =
      (osContractionSemigroup D hcontr τ hτ).comp
        (ℰ.Z (Complex.I * (t : ℂ)) (mul_I_mem_rightHalfPlane t)) := by
  rw [ℰ.map_add (τ : ℂ) (Complex.I * (t : ℂ)) (ofReal_mem_rightHalfPlane hτ)
      (mul_I_mem_rightHalfPlane t), ℰ.real_eq]

def realTimeUnitary (ℰ : OSHolomorphicSemigroup D hcontr) (t : ℝ) :
    OSHilbert D →L[ℂ] OSHilbert D :=
  ℰ.Z (Complex.I * (t : ℂ)) (mul_I_mem_rightHalfPlane t)

@[simp]
theorem realTimeUnitary_zero (ℰ : OSHolomorphicSemigroup D hcontr) :
    ℰ.realTimeUnitary 0 = ContinuousLinearMap.id ℂ (OSHilbert D) := by
  unfold realTimeUnitary
  have h0 : Complex.I * ((0 : ℝ) : ℂ) = 0 := by simp
  have h_congr : ℰ.Z (Complex.I * ((0 : ℝ) : ℂ)) (mul_I_mem_rightHalfPlane 0) =
      ℰ.Z 0 zero_mem_rightHalfPlane := by
    congr 1
  rw [h_congr, ℰ.map_zero]

theorem realTimeUnitary_add (ℰ : OSHolomorphicSemigroup D hcontr) (t₁ t₂ : ℝ) :
    ℰ.realTimeUnitary (t₁ + t₂) =
      (ℰ.realTimeUnitary t₁).comp (ℰ.realTimeUnitary t₂) := by
  unfold realTimeUnitary
  have h_eq : Complex.I * ((t₁ + t₂ : ℝ) : ℂ) =
      Complex.I * (t₁ : ℂ) + Complex.I * (t₂ : ℂ) := by
    push_cast; ring
  have h_congr : ℰ.Z (Complex.I * ((t₁ + t₂ : ℝ) : ℂ)) (mul_I_mem_rightHalfPlane (t₁ + t₂)) =
      ℰ.Z (Complex.I * (t₁ : ℂ) + Complex.I * (t₂ : ℂ))
        (add_mem_rightHalfPlane (mul_I_mem_rightHalfPlane t₁) (mul_I_mem_rightHalfPlane t₂)) := by
    congr 1
  rw [h_congr, ℰ.map_add]

@[simp]
theorem realTimeUnitary_vacuum (ℰ : OSHolomorphicSemigroup D hcontr) (t : ℝ) :
    ℰ.realTimeUnitary t (osVacuum D) = osVacuum D :=
  ℰ.vacuum _ _

theorem realTimeUnitary_neg_comp (ℰ : OSHolomorphicSemigroup D hcontr) (t : ℝ) :
    (ℰ.realTimeUnitary (-t)).comp (ℰ.realTimeUnitary t) =
      ContinuousLinearMap.id ℂ (OSHilbert D) := by
  rw [← ℰ.realTimeUnitary_add, neg_add_cancel, ℰ.realTimeUnitary_zero]

theorem realTimeUnitary_comp_neg (ℰ : OSHolomorphicSemigroup D hcontr) (t : ℝ) :
    (ℰ.realTimeUnitary t).comp (ℰ.realTimeUnitary (-t)) =
      ContinuousLinearMap.id ℂ (OSHilbert D) := by
  rw [← ℰ.realTimeUnitary_add, add_neg_cancel, ℰ.realTimeUnitary_zero]

theorem inner_realTimeUnitary (ℰ : OSHolomorphicSemigroup D hcontr)
    (t : ℝ) (x y : OSHilbert D) :
    ⟪ℰ.realTimeUnitary t x, ℰ.realTimeUnitary t y⟫_ℂ = ⟪x, y⟫_ℂ := by
  unfold realTimeUnitary
  rw [ℰ.adjoint_symm]
  have h_star : star (Complex.I * (t : ℂ)) = Complex.I * ((-t : ℝ) : ℂ) := by
    simp [Complex.conj_I, mul_comm]
  have h_congr : ℰ.Z (star (Complex.I * (t : ℂ)))
      (star_mem_rightHalfPlane (mul_I_mem_rightHalfPlane t)) =
      ℰ.realTimeUnitary (-t) := by
    unfold realTimeUnitary
    congr 1
  rw [h_congr]
  change ⟪x, ((ℰ.realTimeUnitary (-t)).comp (ℰ.realTimeUnitary t)) y⟫_ℂ = ⟪x, y⟫_ℂ
  rw [ℰ.realTimeUnitary_neg_comp, ContinuousLinearMap.id_apply]

@[simp]
theorem norm_realTimeUnitary (ℰ : OSHolomorphicSemigroup D hcontr)
    (t : ℝ) (x : OSHilbert D) :
    ‖ℰ.realTimeUnitary t x‖ = ‖x‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ),
      ℰ.inner_realTimeUnitary t x x]

end OSHolomorphicSemigroup

def spatialPart (a : Fin 4 → ℝ) : Fin 3 → ℝ :=
  fun i => a i.succ

@[simp]
lemma spatialPart_zero : spatialPart 0 = 0 := rfl

@[simp]
lemma spatialPart_add (a b : Fin 4 → ℝ) :
    spatialPart (a + b) = spatialPart a + spatialPart b := rfl

@[simp]
lemma spatialPart_euclidSpatialVec (a : Fin 3 → ℝ) :
    spatialPart (euclidSpatialVec a) = a := by
  ext i
  simp [spatialPart, euclidSpatialVec]

omit [Fintype ι] [DecidableEq ι] in
lemma osConfigSpatialShift_zero :
    osConfigSpatialShift (ι := ι) 0 = id := by
  ext A : 1
  rcases A with ⟨m, α, ⟨y, hy⟩⟩
  dsimp [osConfigSpatialShift]
  congr 2
  ext i μ
  simp [euclidSpatialVec_zero]

omit [Fintype ι] [DecidableEq ι] in
lemma osConfigSpatialShift_add (a b : Fin 3 → ℝ) :
    osConfigSpatialShift (ι := ι) (a + b) =
      osConfigSpatialShift a ∘ osConfigSpatialShift b := by
  ext A : 1
  rcases A with ⟨m, α, ⟨y, hy⟩⟩
  dsimp [osConfigSpatialShift]
  congr 2
  ext i μ
  change (y i + euclidSpatialVec (a + b)) μ = (y i + euclidSpatialVec b + euclidSpatialVec a) μ
  rw [euclidSpatialVec_add]
  simp only [Pi.add_apply]
  ring

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma osConfigSpatialShift_vacuum (a : Fin 3 → ℝ) :
    osConfigSpatialShift a (osVacuumConfig ι) = osVacuumConfig ι := by
  dsimp [osConfigSpatialShift, osVacuumConfig]
  congr 2
  ext i
  exact Fin.elim0 i

@[simp]
theorem osSpatialTranslateLM_zero {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) :
    osSpatialTranslateLM D 0 = LinearMap.id := by
  unfold osSpatialTranslateLM
  rw [osConfigSpatialShift_zero, osLiftConfigMap_id]

theorem osSpatialTranslateLM_add {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (a b : Fin 3 → ℝ) :
    osSpatialTranslateLM D (a + b) =
      (osSpatialTranslateLM D a).comp (osSpatialTranslateLM D b) := by
  unfold osSpatialTranslateLM
  rw [osConfigSpatialShift_add, osLiftConfigMap_comp]

@[simp]
theorem osSpatialTranslateLM_vacuumPre {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (a : Fin 3 → ℝ) :
    osSpatialTranslateLM D a (osVacuumPre D) = osVacuumPre D := by
  dsimp [osSpatialTranslateLM, osVacuumPre]
  rw [osLiftConfigMap_osBasisPre, osConfigSpatialShift_vacuum]

@[simp]
theorem osSpatialTranslate_zero {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (htrans : OSTranslationInvariant D.𝒮) :
    osSpatialTranslate D htrans 0 = ContinuousLinearMap.id ℂ (OSHilbert D) := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih Ψ =>
    change osSpatialTranslate D htrans 0 (toOSHilbert D Ψ) = toOSHilbert D Ψ
    rw [osSpatialTranslate_toOSHilbert, osSpatialTranslateLM_zero, LinearMap.id_apply]

theorem osSpatialTranslate_add {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (htrans : OSTranslationInvariant D.𝒮)
    (a b : Fin 3 → ℝ) :
    osSpatialTranslate D htrans (a + b) =
      (osSpatialTranslate D htrans a).comp (osSpatialTranslate D htrans b) := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih Ψ =>
    change osSpatialTranslate D htrans (a + b) (toOSHilbert D Ψ) =
      osSpatialTranslate D htrans a (osSpatialTranslate D htrans b (toOSHilbert D Ψ))
    rw [osSpatialTranslate_toOSHilbert, osSpatialTranslate_toOSHilbert,
        osSpatialTranslate_toOSHilbert, osSpatialTranslateLM_add, LinearMap.comp_apply]

@[simp]
theorem osSpatialTranslate_vacuum {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (htrans : OSTranslationInvariant D.𝒮)
    (a : Fin 3 → ℝ) :
    osSpatialTranslate D htrans a (osVacuum D) = osVacuum D := by
  dsimp [osVacuum]
  rw [osSpatialTranslate_toOSHilbert, osSpatialTranslateLM_vacuumPre]

namespace OSHolomorphicSemigroup

variable {R : HolomorphicLorentzRep ι} {S : StarStructure R}
  {D : OSReflectionPositiveData R S} {hcontr : OSContractionCondition D}

theorem comm_realTimeUnitary_spatial (ℰ : OSHolomorphicSemigroup D hcontr)
    (htrans : OSTranslationInvariant D.𝒮) (a : Fin 3 → ℝ) (t : ℝ) :
    (osSpatialTranslate D htrans a).comp (ℰ.realTimeUnitary t) =
      (ℰ.realTimeUnitary t).comp (osSpatialTranslate D htrans a) :=
  ℰ.comm_spatial htrans a (Complex.I * (t : ℂ)) (mul_I_mem_rightHalfPlane t)

def spacetimeTranslate (ℰ : OSHolomorphicSemigroup D hcontr)
    (htrans : OSTranslationInvariant D.𝒮) (a : Fin 4 → ℝ) :
    OSHilbert D →L[ℂ] OSHilbert D :=
  (ℰ.realTimeUnitary (a 0)).comp (osSpatialTranslate D htrans (spatialPart a))

@[simp]
theorem spacetimeTranslate_zero (ℰ : OSHolomorphicSemigroup D hcontr)
    (htrans : OSTranslationInvariant D.𝒮) :
    ℰ.spacetimeTranslate htrans 0 = ContinuousLinearMap.id ℂ (OSHilbert D) := by
  unfold spacetimeTranslate
  simp [spatialPart_zero, ℰ.realTimeUnitary_zero, osSpatialTranslate_zero]

theorem spacetimeTranslate_add (ℰ : OSHolomorphicSemigroup D hcontr)
    (htrans : OSTranslationInvariant D.𝒮) (a b : Fin 4 → ℝ) :
    ℰ.spacetimeTranslate htrans (a + b) =
      (ℰ.spacetimeTranslate htrans a).comp (ℰ.spacetimeTranslate htrans b) := by
  unfold spacetimeTranslate
  rw [Pi.add_apply, spatialPart_add, ℰ.realTimeUnitary_add, osSpatialTranslate_add]
  ext x
  simp only [ContinuousLinearMap.comp_apply]
  have h_comm := ℰ.comm_realTimeUnitary_spatial htrans (spatialPart a) (b 0)
  have h_comm_x := congrArg (fun L => L (osSpatialTranslate D htrans (spatialPart b) x)) h_comm
  dsimp at h_comm_x
  rw [← h_comm_x]

@[simp]
theorem spacetimeTranslate_vacuum (ℰ : OSHolomorphicSemigroup D hcontr)
    (htrans : OSTranslationInvariant D.𝒮) (a : Fin 4 → ℝ) :
    ℰ.spacetimeTranslate htrans a (osVacuum D) = osVacuum D := by
  unfold spacetimeTranslate
  simp [osSpatialTranslate_vacuum, ℰ.realTimeUnitary_vacuum]

theorem inner_spacetimeTranslate (ℰ : OSHolomorphicSemigroup D hcontr)
    (htrans : OSTranslationInvariant D.𝒮) (a : Fin 4 → ℝ) (x y : OSHilbert D) :
    ⟪ℰ.spacetimeTranslate htrans a x, ℰ.spacetimeTranslate htrans a y⟫_ℂ = ⟪x, y⟫_ℂ := by
  unfold spacetimeTranslate
  simp only [ContinuousLinearMap.comp_apply]
  rw [ℰ.inner_realTimeUnitary, inner_osSpatialTranslate]

@[simp]
theorem norm_spacetimeTranslate (ℰ : OSHolomorphicSemigroup D hcontr)
    (htrans : OSTranslationInvariant D.𝒮) (a : Fin 4 → ℝ) (x : OSHilbert D) :
    ‖ℰ.spacetimeTranslate htrans a x‖ = ‖x‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ),
      ℰ.inner_spacetimeTranslate htrans a x x]

def complexSpacetimeStep (ℰ : OSHolomorphicSemigroup D hcontr)
    (htrans : OSTranslationInvariant D.𝒮) (z : ℂ) (hz : z ∈ rightHalfPlane) (a : Fin 3 → ℝ) :
    OSHilbert D →L[ℂ] OSHilbert D :=
  (ℰ.Z z hz).comp (osSpatialTranslate D htrans a)

theorem norm_complexSpacetimeStep_le (ℰ : OSHolomorphicSemigroup D hcontr)
    (htrans : OSTranslationInvariant D.𝒮) (z : ℂ) (hz : z ∈ rightHalfPlane)
    (a : Fin 3 → ℝ) (x : OSHilbert D) :
    ‖ℰ.complexSpacetimeStep htrans z hz a x‖ ≤ ‖x‖ := by
  unfold complexSpacetimeStep
  simp only [ContinuousLinearMap.comp_apply]
  have h1 := ℰ.contraction z hz (osSpatialTranslate D htrans a x)
  have h2 : ‖osSpatialTranslate D htrans a x‖ = ‖x‖ := by
    rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ),
        inner_osSpatialTranslate D htrans a x x]
  exact h1.trans_eq h2

theorem complexSpacetimeStep_real_zero_eq_contraction (ℰ : OSHolomorphicSemigroup D hcontr)
    (htrans : OSTranslationInvariant D.𝒮) (τ : ℝ) (hτ : 0 ≤ τ) :
    ℰ.complexSpacetimeStep htrans (τ : ℂ) (ofReal_mem_rightHalfPlane hτ) 0 =
      osContractionSemigroup D hcontr τ hτ := by
  unfold complexSpacetimeStep
  rw [ℰ.real_eq, osSpatialTranslate_zero, ContinuousLinearMap.comp_id]

theorem complexSpacetimeStep_imag_eq_spacetimeTranslate (ℰ : OSHolomorphicSemigroup D hcontr)
    (htrans : OSTranslationInvariant D.𝒮) (a : Fin 4 → ℝ) :
    ℰ.complexSpacetimeStep htrans (Complex.I * (a 0 : ℂ))
      (mul_I_mem_rightHalfPlane (a 0)) (spatialPart a) =
      ℰ.spacetimeTranslate htrans a := rfl

end OSHolomorphicSemigroup

lemma timeUnitVec_mem_forward_light_cone :
    euclidTimeVec 1 ∈ forward_light_cone := by
  dsimp [forward_light_cone]
  rw [minkowskiInner_explicit]
  simp [euclidTimeVec]

omit [Fintype ι] [DecidableEq ι] in
theorem wightman_eq_of_tubeExtension_eq {W₁ W₂ : WightmanFamily ι}
    (E₁ : TubeExtension W₁) (E₂ : TubeExtension W₂)
    (hH : ∀ (n : ℕ) (α : Fin n → ι) (z : Fin n → Fin 4 → ℂ),
      z ∈ forward_tube_n n → E₁.H n α z = E₂.H n α z) :
    W₁ = W₂ := by
  ext n α f
  have hv : euclidTimeVec 1 ∈ forward_light_cone := timeUnitVec_mem_forward_light_cone
  have hb₁ := E₁.boundary n α f (euclidTimeVec 1) hv
  have hb₂ := E₂.boundary n α f (euclidTimeVec 1) hv
  have h_ev : (fun t : ℝ => ∫ x : Fin n → Fin 4 → ℝ,
      E₁.H n α (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * euclidTimeVec 1 k : ℝ) : ℂ)) *
        f x) =ᶠ[𝓝[>] (0 : ℝ)]
    (fun t : ℝ => ∫ x : Fin n → Fin 4 → ℝ,
      E₂.H n α (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * euclidTimeVec 1 k : ℝ) : ℂ)) *
        f x) := by
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    congr 1
    ext x
    congr 1
    apply hH n α
    intro i hi
    change (fun k : Fin 4 => -((((fun j m => (x j m : ℂ) +
        Complex.I * ((t * (j : ℕ) * euclidTimeVec 1 m : ℝ) : ℂ)) i -
      (fun j m => (x j m : ℂ) +
        Complex.I * ((t * (j : ℕ) * euclidTimeVec 1 m : ℝ) : ℂ)) ⟨i.val + 1, hi⟩) k).im)) ∈
      forward_light_cone
    have h_im : (fun k : Fin 4 => -((((fun j m => (x j m : ℂ) +
          Complex.I * ((t * (j : ℕ) * euclidTimeVec 1 m : ℝ) : ℂ)) i -
        (fun j m => (x j m : ℂ) +
          Complex.I * ((t * (j : ℕ) * euclidTimeVec 1 m : ℝ) : ℂ)) ⟨i.val + 1, hi⟩) k).im)) =
        fun k : Fin 4 => if k = 0 then t else 0 := by
      ext k
      fin_cases k <;> · simp [euclidTimeVec, Complex.sub_im, Complex.add_im]; try ring
    rw [h_im]
    dsimp [forward_light_cone]
    rw [minkowskiInner_explicit]
    simp only [↓reduceIte, Fin.isValue, Fin.reduceEq, mul_zero, sub_zero]
    exact ⟨ht, mul_pos ht ht⟩
  haveI : NeBot (𝓝[>] (0 : ℝ)) := nhdsWithin_Ioi_neBot le_rfl
  exact tendsto_nhds_unique (hb₁.congr' h_ev) hb₂

omit [Fintype ι] [DecidableEq ι] in
def ForwardTubeRigidFromEuclid {W₁ W₂ : WightmanFamily ι}
    (E₁ : TubeExtension W₁) (E₂ : TubeExtension W₂) : Prop :=
  (∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
    x ∈ orderedEuclidN n → schwingerFromTube E₁ n α x = schwingerFromTube E₂ n α x) →
  ∀ (n : ℕ) (α : Fin n → ι) (z : Fin n → Fin 4 → ℂ),
    z ∈ forward_tube_n n → E₁.H n α z = E₂.H n α z

omit [Fintype ι] [DecidableEq ι] in
theorem wightman_eq_of_schwingerFromTube_eq {W₁ W₂ : WightmanFamily ι}
    (E₁ : TubeExtension W₁) (E₂ : TubeExtension W₂)
    (hrigid : ForwardTubeRigidFromEuclid E₁ E₂)
    (hS : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → schwingerFromTube E₁ n α x = schwingerFromTube E₂ n α x) :
    W₁ = W₂ :=
  wightman_eq_of_tubeExtension_eq E₁ E₂ (hrigid hS)

structure OSReconstructedWightman (R : HolomorphicLorentzRep ι) (S : StarStructure R)
    (η : ℂ) (𝒮 : SchwingerFamily ι) where
  osAxioms : OSAxioms R S η 𝒮
  contraction : OSContractionCondition osAxioms.toReflectionPositiveData
  semigroup : OSHolomorphicSemigroup osAxioms.toReflectionPositiveData contraction
  W : WightmanFamily ι
  E : TubeExtension W
  schwinger_eq : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
    x ∈ orderedEuclidN n → 𝒮 n α x = schwingerFromTube E n α x
  tube_covariant : TubeCovariant R E
  tube_weakLocality : TubeWeakLocality η E
  spectrum : SpectrumCondition W
  poincare : PoincareCovariant R W
  weakLocality : WeakLocality η W
  positivity : Positivity S W

namespace OSReconstructedWightman

variable {R : HolomorphicLorentzRep ι} {S : StarStructure R}
  {η : ℂ} {𝒮 : SchwingerFamily ι}

theorem wightman_unique (P₁ P₂ : OSReconstructedWightman R S η 𝒮)
    (hrigid : ForwardTubeRigidFromEuclid P₁.E P₂.E) :
    P₁.W = P₂.W := by
  apply wightman_eq_of_schwingerFromTube_eq P₁.E P₂.E hrigid
  intro n α x hx
  rw [← P₁.schwinger_eq n α x hx, ← P₂.schwinger_eq n α x hx]

theorem complexCovariant (P : OSReconstructedWightman R S η 𝒮) :
    ComplexCovariant R P.E :=
  complex_covariance_of_real R P.W P.E P.tube_covariant

theorem tube_pct (P : OSReconstructedWightman R S η 𝒮)
    (n : ℕ) (z : Fin n → Fin 4 → ℂ)
    (hz : z ∈ forward_tube_n n) (h_neg_z : -z ∈ forward_tube_n n)
    (α : Fin n → ι) :
    P.E.H n α (-(z ∘ Fin.rev)) =
      η ^ (n * (n - 1) / 2) *
        ∑ β : Fin n → ι, (∏ i, R.σ (-1, 1) (α i) (β i)) * P.E.H n (β ∘ Fin.rev) (-z) :=
  tube_pct_theorem R P.W P.E P.complexCovariant P.tube_weakLocality n z hz h_neg_z α

theorem wightman_pct (P : OSReconstructedWightman R S η 𝒮) :
    WightmanPCT η R P.W :=
  wightman_pct_theorem R P.W P.spectrum P.poincare P.weakLocality

theorem schwinger_spin_parity_selection (P : OSReconstructedWightman R S η 𝒮)
    {ε : ℂ} (hε : R.HasSpinParity ε)
    (n : ℕ) (x : Fin n → Fin 4 → ℝ) (hx : x ∈ orderedEuclidN n) (α : Fin n → ι) :
    𝒮 n α x = ε ^ n * 𝒮 n α x := by
  rw [P.schwinger_eq n α x hx]
  exact schwingerFromTube_spin_parity_selection R P.W P.E P.tube_covariant hε n x hx α

theorem schwinger_eq_zero_of_odd_fermion (P : OSReconstructedWightman R S η 𝒮)
    (hε : R.HasSpinParity (-1))
    (n : ℕ) (hn : Odd n) (x : Fin n → Fin 4 → ℝ) (hx : x ∈ orderedEuclidN n)
    (α : Fin n → ι) :
    𝒮 n α x = 0 := by
  rw [P.schwinger_eq n α x hx]
  exact schwingerFromTube_eq_zero_of_odd_fermion R P.W P.E P.tube_covariant hε n hn x hx α

theorem spin_statistics_from_schwinger (P : OSReconstructedWightman R S η 𝒮)
    {ε : ℂ} (hε : R.HasSpinParity ε)
    (h_exch : TwoPointSpinExchange ε P.E)
    (h_nondeg : ∃ (α : Fin 2 → ι) (x : Fin 2 → Fin 4 → ℝ),
      x ∈ orderedEuclidN 2 ∧ 𝒮 2 (α ∘ Fin.rev) x ≠ 0) :
    η = ε := by
  rcases h_nondeg with ⟨α, x, hx, hne⟩
  rw [P.schwinger_eq 2 (α ∘ Fin.rev) x hx] at hne
  exact schwinger_spin_statistics_theorem R P.W P.E hε P.tube_weakLocality h_exch ⟨α, x, hx, hne⟩

theorem spin_statistics_distributional (P : OSReconstructedWightman R S η 𝒮)
    {ε : ℂ} (hε : R.HasSpinParity ε)
    (h_exch : DistributionalTwoPointSpinExchange ε P.W)
    (h_nondeg : ∃ (α : Fin 2 → ι) (f f' : SchwartzMap (Fin 2 → Fin 4 → ℝ) ℂ),
      (∀ x, f x ≠ 0 → x ∈ jost_points_n 2) ∧
      (∀ x : Fin 2 → Fin 4 → ℝ, f' (fun i => x (Fin.rev i)) = f x) ∧
      P.W 2 (α ∘ Fin.rev) f' ≠ 0) :
    η = ε :=
  spin_statistics_theorem R P.W hε P.weakLocality h_exch h_nondeg

end OSReconstructedWightman

def vladimirovOSReconstruction (R : HolomorphicLorentzRep ι) (S : StarStructure R)
    (W : WightmanFamily ι) {η : ℂ}
    (hspec : SpectrumCondition W) (hP : PoincareCovariant R W)
    (hloc : WeakLocality η W) (hpos : Positivity S W)
    (hherm : TubeWickHermiticity S (vladimirovTubeExtension R W hspec hP))
    (hrp : OSReflectionPositive S (vladimirovSchwinger W))
    (hcontr : OSContractionCondition
      { 𝒮 := vladimirovSchwinger W
        hermiticity := schwingerFromTube_os_hermiticity S _ hherm
        positivity := hrp })
    (ℰ : OSHolomorphicSemigroup
      { 𝒮 := vladimirovSchwinger W
        hermiticity := schwingerFromTube_os_hermiticity S _ hherm
        positivity := hrp }
      hcontr) :
    OSReconstructedWightman R S η (vladimirovSchwinger W) where
  osAxioms := schwingerFromTube_osAxioms R S W (vladimirovTubeExtension R W hspec hP)
    (vladimirov_tubeTranslationInvariant R W hspec hP)
    (vladimirov_tubeCovariant R W hspec hP)
    hherm
    (vladimirov_tubeWeakLocality R W hspec hP hloc) hrp
  contraction := hcontr
  semigroup := ℰ
  W := W
  E := vladimirovTubeExtension R W hspec hP
  schwinger_eq := fun _ _ _ _ => rfl
  tube_covariant := vladimirov_tubeCovariant R W hspec hP
  tube_weakLocality := vladimirov_tubeWeakLocality R W hspec hP hloc
  spectrum := hspec
  poincare := hP
  weakLocality := hloc
  positivity := hpos

theorem osterwalder_schrader_master_theorem
    (R : HolomorphicLorentzRep ι) (S : StarStructure R) (η : ℂ) (𝒮 : SchwingerFamily ι)
    (P : OSReconstructedWightman R S η 𝒮) :
    (∀ a b : Fin 4 → ℝ,
      P.semigroup.spacetimeTranslate P.osAxioms.os1_translation (a + b) =
        (P.semigroup.spacetimeTranslate P.osAxioms.os1_translation a).comp
          (P.semigroup.spacetimeTranslate P.osAxioms.os1_translation b)) ∧
    (∀ a : Fin 4 → ℝ,
      P.semigroup.spacetimeTranslate P.osAxioms.os1_translation a
        (osVacuum P.osAxioms.toReflectionPositiveData) =
        osVacuum P.osAxioms.toReflectionPositiveData) ∧
    ComplexCovariant R P.E ∧
    WightmanPCT η R P.W :=
  ⟨P.semigroup.spacetimeTranslate_add P.osAxioms.os1_translation,
   P.semigroup.spacetimeTranslate_vacuum P.osAxioms.os1_translation,
   P.complexCovariant,
   P.wightman_pct⟩

def wickFlatLinearEquiv (n : ℕ) : (Fin n × Fin 4 → ℂ) ≃ₗ[ℂ] (Fin n → Fin 4 → ℂ) where
  toFun w i μ := if μ = 0 then w (i, 0) * Complex.I else w (i, μ)
  map_add' w₁ w₂ := by
    ext i μ
    dsimp
    split_ifs <;> ring
  map_smul' c w := by
    ext i μ
    dsimp
    split_ifs <;> ring
  invFun z p := if p.2 = 0 then -Complex.I * z p.1 0 else z p.1 p.2
  left_inv w := by
    ext ⟨i, μ⟩
    dsimp
    split_ifs with h
    · subst h
      calc -Complex.I * (w (i, 0) * Complex.I)
          = -(Complex.I * Complex.I) * w (i, 0) := by ring
        _ = w (i, 0) := by rw [Complex.I_mul_I]; ring
    · rfl
  right_inv z := by
    ext i μ
    dsimp
    split_ifs with h
    · subst h
      calc (-Complex.I * z i 0) * Complex.I
          = -(Complex.I * Complex.I) * z i 0 := by ring
        _ = z i 0 := by rw [Complex.I_mul_I]; ring
    · rfl

def wickFlatCLE (n : ℕ) : (Fin n × Fin 4 → ℂ) ≃L[ℂ] (Fin n → Fin 4 → ℂ) :=
  (wickFlatLinearEquiv n).toContinuousLinearEquiv

def ofRealFlat (n : ℕ) : (Fin n × Fin 4 → ℝ) →L[ℝ] (Fin n × Fin 4 → ℂ) :=
  ContinuousLinearMap.pi
    (fun p => ContinuousLinearMap.comp Complex.ofRealCLM (ContinuousLinearMap.proj p))

lemma ofRealFlat_apply (n : ℕ) (t : Fin n × Fin 4 → ℝ) :
    ofRealFlat n t = fun p => (t p : ℂ) := rfl

lemma wickFlatCLE_ofRealFlat (n : ℕ) (t : Fin n × Fin 4 → ℝ) :
    wickFlatCLE n (ofRealFlat n t) = wickEmbedN n (fun i μ => t (i, μ)) := by
  ext i μ
  change (if μ = 0 then (t (i, 0) : ℂ) * Complex.I else (t (i, μ) : ℂ)) =
    wickEmbed (fun m => t (i, m)) μ
  fin_cases μ <;> simp [wickEmbed]

lemma wickFlatCLE_ofRealFlat_uncurry (n : ℕ) (x : Fin n → Fin 4 → ℝ) :
    wickFlatCLE n (ofRealFlat n (fun p => x p.1 p.2)) = wickEmbedN n x := by
  rw [wickFlatCLE_ofRealFlat]

lemma wickFlatCLE_symm_wickEmbedN (n : ℕ) (x : Fin n → Fin 4 → ℝ) :
    (wickFlatCLE n).symm (wickEmbedN n x) = ofRealFlat n (fun p => x p.1 p.2) := by
  rw [← wickFlatCLE_ofRealFlat_uncurry n x]
  exact (wickFlatCLE n).symm_apply_apply _

theorem analyticOn_forward_tube_eq_of_eventuallyEq_wickEmbedN (n : ℕ)
    {f g : (Fin n → Fin 4 → ℂ) → ℂ}
    (hf : AnalyticOn ℂ f (forward_tube_n n))
    (hg : AnalyticOn ℂ g (forward_tube_n n))
    {x₀ : Fin n → Fin 4 → ℝ} (hx₀ : x₀ ∈ orderedEuclidN n)
    (h_ev : ∀ᶠ x in 𝓝 x₀, f (wickEmbedN n x) = g (wickEmbedN n x)) :
    Set.EqOn f g (forward_tube_n n) := by
  let a₀ : Fin n × Fin 4 → ℝ := fun p => x₀ p.1 p.2
  let z₀ : Fin n → Fin 4 → ℂ := wickEmbedN n x₀
  have hz₀ : z₀ ∈ forward_tube_n n := wickEmbedN_mem_forward_tube_n n hx₀
  have hw₀ : wickFlatCLE n (ofRealFlat n a₀) = z₀ :=
    wickFlatCLE_ofRealFlat_uncurry n x₀
  have hf_z₀ : AnalyticAt ℂ f z₀ :=
    hf.analyticAt ((forward_tube_n_isOpen n).mem_nhds hz₀)
  have hg_z₀ : AnalyticAt ℂ g z₀ :=
    hg.analyticAt ((forward_tube_n_isOpen n).mem_nhds hz₀)
  have hf_comp : AnalyticAt ℂ (fun w => f (wickFlatCLE n w)) (ofRealFlat n a₀) := by
    have hf' : AnalyticAt ℂ f (wickFlatCLE n (ofRealFlat n a₀)) := hw₀.symm ▸ hf_z₀
    exact hf'.comp ((wickFlatCLE n).toContinuousLinearMap.analyticAt (ofRealFlat n a₀))
  have hg_comp : AnalyticAt ℂ (fun w => g (wickFlatCLE n w)) (ofRealFlat n a₀) := by
    have hg' : AnalyticAt ℂ g (wickFlatCLE n (ofRealFlat n a₀)) := hw₀.symm ▸ hg_z₀
    exact hg'.comp ((wickFlatCLE n).toContinuousLinearMap.analyticAt (ofRealFlat n a₀))
  have h_uncurry_cont :
      Continuous (fun (t : Fin n × Fin 4 → ℝ) (i : Fin n) (μ : Fin 4) => t (i, μ)) :=
    continuous_pi (fun i => continuous_pi (fun μ => continuous_apply (i, μ)))
  have h_tendsto_uncurry :
      Tendsto (fun (t : Fin n × Fin 4 → ℝ) (i : Fin n) (μ : Fin 4) => t (i, μ))
        (𝓝 a₀) (𝓝 x₀) :=
    h_uncurry_cont.tendsto a₀
  have h_real_ev : ∀ᶠ t : Fin n × Fin 4 → ℝ in 𝓝 a₀,
      f (wickFlatCLE n (ofRealFlat n t)) = g (wickFlatCLE n (ofRealFlat n t)) := by
    filter_upwards [h_tendsto_uncurry.eventually h_ev] with t ht
    rw [wickFlatCLE_ofRealFlat]
    exact ht
  have h_nhds_flat := Analysis.analytic_nhds_eq_of_real_eq_N
    (fun w => f (wickFlatCLE n w)) (fun w => g (wickFlatCLE n w))
    a₀ (ofRealFlat n) (ofRealFlat_apply n) hf_comp hg_comp h_real_ev
  have h_tendsto : Tendsto (wickFlatCLE n).symm (𝓝 z₀) (𝓝 (ofRealFlat n a₀)) := by
    rw [← wickFlatCLE_symm_wickEmbedN n x₀]
    exact (wickFlatCLE n).symm.continuous.tendsto z₀
  have h_nhds_z₀ : f =ᶠ[𝓝 z₀] g := by
    filter_upwards [h_tendsto.eventually h_nhds_flat] with z hz
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using hz
  have hf_nhd : AnalyticOnNhd ℂ f (forward_tube_n n) :=
    (forward_tube_n_isOpen n).analyticOn_iff_analyticOnNhd.mp hf
  have hg_nhd : AnalyticOnNhd ℂ g (forward_tube_n n) :=
    (forward_tube_n_isOpen n).analyticOn_iff_analyticOnNhd.mp hg
  exact hf_nhd.eqOn_of_preconnected_of_eventuallyEq hg_nhd
    (forward_tube_is_connected n).isPreconnected hz₀ h_nhds_z₀

theorem analyticOn_forward_tube_eq_of_posOrderedEuclidN_eq (n : ℕ)
    {f g : (Fin n → Fin 4 → ℂ) → ℂ}
    (hf : AnalyticOn ℂ f (forward_tube_n n))
    (hg : AnalyticOn ℂ g (forward_tube_n n))
    (h_eq : ∀ x ∈ posOrderedEuclidN n, f (wickEmbedN n x) = g (wickEmbedN n x)) :
    Set.EqOn f g (forward_tube_n n) := by
  have hx₀_pos : euclidOrderedBasePoint n ∈ posOrderedEuclidN n :=
    euclidOrderedBasePoint_mem_posOrderedEuclidN n
  apply analyticOn_forward_tube_eq_of_eventuallyEq_wickEmbedN n hf hg hx₀_pos.2
  filter_upwards [(isOpen_posOrderedEuclidN n).mem_nhds hx₀_pos] with x hx
  exact h_eq x hx

theorem analyticOn_forward_tube_eq_of_wickEmbedN_eq (n : ℕ)
    {f g : (Fin n → Fin 4 → ℂ) → ℂ}
    (hf : AnalyticOn ℂ f (forward_tube_n n))
    (hg : AnalyticOn ℂ g (forward_tube_n n))
    (h_eq : ∀ x ∈ orderedEuclidN n, f (wickEmbedN n x) = g (wickEmbedN n x)) :
    Set.EqOn f g (forward_tube_n n) :=
  analyticOn_forward_tube_eq_of_posOrderedEuclidN_eq n hf hg
    (fun x hx => h_eq x (posOrderedEuclidN_subset_orderedEuclidN n hx))

theorem analyticOn_forward_tube_eq_zero_of_posOrderedEuclidN_eq_zero (n : ℕ)
    {f : (Fin n → Fin 4 → ℂ) → ℂ}
    (hf : AnalyticOn ℂ f (forward_tube_n n))
    (h_zero : ∀ x ∈ posOrderedEuclidN n, f (wickEmbedN n x) = 0) :
    ∀ z ∈ forward_tube_n n, f z = 0 :=
  analyticOn_forward_tube_eq_of_posOrderedEuclidN_eq n hf
    (analyticOn_const (v := (0 : ℂ))) h_zero

omit [Fintype ι] [DecidableEq ι] in
theorem forwardTubeRigidFromEuclid_holds {W₁ W₂ : WightmanFamily ι}
    (E₁ : TubeExtension W₁) (E₂ : TubeExtension W₂) :
    ForwardTubeRigidFromEuclid E₁ E₂ := by
  intro hS n α z hz
  exact analyticOn_forward_tube_eq_of_wickEmbedN_eq n
    (E₁.analytic n α) (E₂.analytic n α) (hS n α) hz

omit [Fintype ι] [DecidableEq ι] in
theorem tubeExtension_eq_of_posOrdered_schwingerFromTube_eq {W₁ W₂ : WightmanFamily ι}
    (E₁ : TubeExtension W₁) (E₂ : TubeExtension W₂)
    (hS : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ posOrderedEuclidN n → schwingerFromTube E₁ n α x = schwingerFromTube E₂ n α x)
    (n : ℕ) (α : Fin n → ι) (z : Fin n → Fin 4 → ℂ) (hz : z ∈ forward_tube_n n) :
    E₁.H n α z = E₂.H n α z :=
  analyticOn_forward_tube_eq_of_posOrderedEuclidN_eq n
    (E₁.analytic n α) (E₂.analytic n α) (hS n α) hz

omit [Fintype ι] [DecidableEq ι] in
theorem tubeExtension_eq_of_schwingerFromTube_eq {W₁ W₂ : WightmanFamily ι}
    (E₁ : TubeExtension W₁) (E₂ : TubeExtension W₂)
    (hS : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → schwingerFromTube E₁ n α x = schwingerFromTube E₂ n α x)
    (n : ℕ) (α : Fin n → ι) (z : Fin n → Fin 4 → ℂ) (hz : z ∈ forward_tube_n n) :
    E₁.H n α z = E₂.H n α z :=
  forwardTubeRigidFromEuclid_holds E₁ E₂ hS n α z hz

omit [Fintype ι] [DecidableEq ι] in
theorem wightman_eq_of_schwingerFromTube_eq_unconditional {W₁ W₂ : WightmanFamily ι}
    (E₁ : TubeExtension W₁) (E₂ : TubeExtension W₂)
    (hS : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → schwingerFromTube E₁ n α x = schwingerFromTube E₂ n α x) :
    W₁ = W₂ :=
  wightman_eq_of_schwingerFromTube_eq E₁ E₂ (forwardTubeRigidFromEuclid_holds E₁ E₂) hS

omit [Fintype ι] [DecidableEq ι] in
theorem wightman_eq_of_posOrdered_schwingerFromTube_eq {W₁ W₂ : WightmanFamily ι}
    (E₁ : TubeExtension W₁) (E₂ : TubeExtension W₂)
    (hS : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ posOrderedEuclidN n → schwingerFromTube E₁ n α x = schwingerFromTube E₂ n α x) :
    W₁ = W₂ :=
  wightman_eq_of_tubeExtension_eq E₁ E₂
    (tubeExtension_eq_of_posOrdered_schwingerFromTube_eq E₁ E₂ hS)

omit [Fintype ι] [DecidableEq ι] in
lemma wightman_eq_zero_of_tube_eq_zero {W : WightmanFamily ι} (E : TubeExtension W)
    (n : ℕ) (α : Fin n → ι)
    (hH : ∀ z ∈ forward_tube_n n, E.H n α z = 0)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    W n α f = 0 := by
  have hv : euclidTimeVec 1 ∈ forward_light_cone := timeUnitVec_mem_forward_light_cone
  have hb := E.boundary n α f (euclidTimeVec 1) hv
  have h_ev : (fun t : ℝ => ∫ x : Fin n → Fin 4 → ℝ,
      E.H n α (fun i k => (x i k : ℂ) +
        Complex.I * ((t * (i : ℕ) * euclidTimeVec 1 k : ℝ) : ℂ)) *
        f x) =ᶠ[𝓝[>] (0 : ℝ)] (fun _ : ℝ => (0 : ℂ)) := by
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    have h_int : (fun x : Fin n → Fin 4 → ℝ =>
        E.H n α (fun i k => (x i k : ℂ) +
          Complex.I * ((t * (i : ℕ) * euclidTimeVec 1 k : ℝ) : ℂ)) * f x) =
        fun _ => 0 := by
      ext x
      have hz : (fun i k => (x i k : ℂ) +
          Complex.I * ((t * (i : ℕ) * euclidTimeVec 1 k : ℝ) : ℂ)) ∈ forward_tube_n n := by
        intro i hi
        change (fun k : Fin 4 => -((((fun j m => (x j m : ℂ) +
            Complex.I * ((t * (j : ℕ) * euclidTimeVec 1 m : ℝ) : ℂ)) i -
          (fun j m => (x j m : ℂ) +
            Complex.I * ((t * (j : ℕ) * euclidTimeVec 1 m : ℝ) : ℂ))
              ⟨i.val + 1, hi⟩) k).im)) ∈
          forward_light_cone
        have h_im : (fun k : Fin 4 => -((((fun j m => (x j m : ℂ) +
              Complex.I * ((t * (j : ℕ) * euclidTimeVec 1 m : ℝ) : ℂ)) i -
            (fun j m => (x j m : ℂ) +
              Complex.I * ((t * (j : ℕ) * euclidTimeVec 1 m : ℝ) : ℂ))
                ⟨i.val + 1, hi⟩) k).im)) =
            fun k : Fin 4 => if k = 0 then t else 0 := by
          ext k
          fin_cases k <;> · simp [euclidTimeVec, Complex.sub_im, Complex.add_im]; try ring
        rw [h_im]
        dsimp [forward_light_cone]
        rw [minkowskiInner_explicit]
        simp only [↓reduceIte, Fin.isValue, Fin.reduceEq, mul_zero, sub_zero]
        exact ⟨ht, mul_pos ht ht⟩
      rw [hH _ hz, zero_mul]
    rw [h_int, MeasureTheory.integral_zero]
  haveI : NeBot (𝓝[>] (0 : ℝ)) := nhdsWithin_Ioi_neBot le_rfl
  exact tendsto_nhds_unique (hb.congr' h_ev) tendsto_const_nhds

omit [Fintype ι] [DecidableEq ι] in
theorem exists_posOrderedEuclidN_ne_zero_of_wightman_ne_zero {W : WightmanFamily ι}
    (E : TubeExtension W) (n : ℕ) (α : Fin n → ι)
    {f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ} (hf : W n α f ≠ 0) :
    ∃ x ∈ posOrderedEuclidN n, schwingerFromTube E n α x ≠ 0 := by
  by_contra! h_zero
  have hH_zero : ∀ z ∈ forward_tube_n n, E.H n α z = 0 :=
    analyticOn_forward_tube_eq_zero_of_posOrderedEuclidN_eq_zero n (E.analytic n α) h_zero
  exact hf (wightman_eq_zero_of_tube_eq_zero E n α hH_zero f)

theorem spin_statistics_of_twoPoint_wightman_ne_zero
    (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι) (E : TubeExtension W)
    {η ε : ℂ} (hε : R.HasSpinParity ε)
    (hloc : TubeWeakLocality η E)
    (h_exch : TwoPointSpinExchange ε E)
    (h_nondeg : ∃ (α : Fin 2 → ι) (f : SchwartzMap (Fin 2 → Fin 4 → ℝ) ℂ), W 2 α f ≠ 0) :
    η = ε := by
  rcases h_nondeg with ⟨α, f, hf⟩
  rcases exists_posOrderedEuclidN_ne_zero_of_wightman_ne_zero E 2 α hf with ⟨x, hx, hne⟩
  have h_rev : (α ∘ Fin.rev) ∘ Fin.rev = α := by
    ext i
    simp [Fin.rev_rev]
  refine schwinger_spin_statistics_theorem R W E hε hloc h_exch
    ⟨α ∘ Fin.rev, x, posOrderedEuclidN_subset_orderedEuclidN 2 hx, ?_⟩
  rw [h_rev]
  exact hne

theorem vladimirovSchwinger_eq_imp_wightman_eq (R : HolomorphicLorentzRep ι)
    {W₁ W₂ : WightmanFamily ι}
    (hspec₁ : SpectrumCondition W₁) (hP₁ : PoincareCovariant R W₁)
    (hspec₂ : SpectrumCondition W₂) (hP₂ : PoincareCovariant R W₂)
    (hS : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → vladimirovSchwinger W₁ n α x = vladimirovSchwinger W₂ n α x) :
    W₁ = W₂ :=
  wightman_eq_of_schwingerFromTube_eq_unconditional
    (vladimirovTubeExtension R W₁ hspec₁ hP₁)
    (vladimirovTubeExtension R W₂ hspec₂ hP₂) hS

theorem vladimirovSchwinger_posOrdered_eq_imp_wightman_eq (R : HolomorphicLorentzRep ι)
    {W₁ W₂ : WightmanFamily ι}
    (hspec₁ : SpectrumCondition W₁) (hP₁ : PoincareCovariant R W₁)
    (hspec₂ : SpectrumCondition W₂) (hP₂ : PoincareCovariant R W₂)
    (hS : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ posOrderedEuclidN n → vladimirovSchwinger W₁ n α x = vladimirovSchwinger W₂ n α x) :
    W₁ = W₂ :=
  wightman_eq_of_posOrdered_schwingerFromTube_eq
    (vladimirovTubeExtension R W₁ hspec₁ hP₁)
    (vladimirovTubeExtension R W₂ hspec₂ hP₂) hS

namespace OSReconstructedWightman

variable {R : HolomorphicLorentzRep ι} {S : StarStructure R}
  {η : ℂ} {𝒮 : SchwingerFamily ι}

theorem tube_H_unique (P₁ P₂ : OSReconstructedWightman R S η 𝒮)
    (n : ℕ) (α : Fin n → ι) (z : Fin n → Fin 4 → ℂ) (hz : z ∈ forward_tube_n n) :
    P₁.E.H n α z = P₂.E.H n α z := by
  apply tubeExtension_eq_of_schwingerFromTube_eq P₁.E P₂.E _ n α z hz
  intro m β x hx
  rw [← P₁.schwinger_eq m β x hx, ← P₂.schwinger_eq m β x hx]

theorem wightman_unique_unconditional (P₁ P₂ : OSReconstructedWightman R S η 𝒮) :
    P₁.W = P₂.W :=
  P₁.wightman_unique P₂ (forwardTubeRigidFromEuclid_holds P₁.E P₂.E)

theorem spin_statistics_of_twoPoint_ne_zero (P : OSReconstructedWightman R S η 𝒮)
    {ε : ℂ} (hε : R.HasSpinParity ε)
    (h_exch : TwoPointSpinExchange ε P.E)
    (h_nondeg : ∃ (α : Fin 2 → ι) (f : SchwartzMap (Fin 2 → Fin 4 → ℝ) ℂ), P.W 2 α f ≠ 0) :
    η = ε :=
  spin_statistics_of_twoPoint_wightman_ne_zero R P.W P.E hε P.tube_weakLocality h_exch h_nondeg

end OSReconstructedWightman

theorem osterwalder_schrader_complete_master_theorem
    (R : HolomorphicLorentzRep ι) (S : StarStructure R) (η : ℂ) (𝒮 : SchwingerFamily ι)
    (P : OSReconstructedWightman R S η 𝒮) :
    (∀ a b : Fin 4 → ℝ,
      P.semigroup.spacetimeTranslate P.osAxioms.os1_translation (a + b) =
        (P.semigroup.spacetimeTranslate P.osAxioms.os1_translation a).comp
          (P.semigroup.spacetimeTranslate P.osAxioms.os1_translation b)) ∧
    (∀ a : Fin 4 → ℝ,
      P.semigroup.spacetimeTranslate P.osAxioms.os1_translation a
        (osVacuum P.osAxioms.toReflectionPositiveData) =
        osVacuum P.osAxioms.toReflectionPositiveData) ∧
    ComplexCovariant R P.E ∧
    WightmanPCT η R P.W ∧
    (∀ P' : OSReconstructedWightman R S η 𝒮,
      P'.W = P.W ∧
      ∀ (n : ℕ) (α : Fin n → ι) (z : Fin n → Fin 4 → ℂ),
        z ∈ forward_tube_n n → P'.E.H n α z = P.E.H n α z) :=
  ⟨P.semigroup.spacetimeTranslate_add P.osAxioms.os1_translation,
   P.semigroup.spacetimeTranslate_vacuum P.osAxioms.os1_translation,
   P.complexCovariant,
   P.wightman_pct,
   fun P' => ⟨P'.wightman_unique_unconditional P, P'.tube_H_unique P⟩⟩

namespace IsPoly

lemma prod {κ : Type*} (s : Finset κ) (f : κ → SL2C × SL2C → ℂ)
    (h : ∀ i ∈ s, IsPoly (f i)) : IsPoly fun p => ∏ i ∈ s, f i p := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const 1
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (h a (by simp)).mul (ih fun i hi => h i (by simp [hi]))

lemma swap {f : SL2C × SL2C → ℂ} (hf : IsPoly f) :
    IsPoly fun p => f (p.2, p.1) := by
  rcases hf with ⟨P, hP⟩
  refine ⟨MvPolynomial.rename Sum.swap P, fun p => ?_⟩
  have h_pt : polyPt (p.2, p.1) = polyPt p ∘ Sum.swap := by
    ext (a | a) <;> rfl
  dsimp
  rw [hP (p.2, p.1), MvPolynomial.eval_rename, h_pt]

end IsPoly

def rightWeylRep : HolomorphicLorentzRep (Fin 2) where
  σ :=
    { toFun := fun p => (p.2 : Matrix (Fin 2) (Fin 2) ℂ)
      map_one' := by simp
      map_mul' := fun p q => by simp }
  polynomial i j := IsPoly.coordB i j

lemma rightWeylRep_spinParity : rightWeylRep.HasSpinParity (-1) := by
  refine ⟨?_, Or.inr rfl⟩
  change ((-1 : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) = (-1 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
  simp [Matrix.SpecialLinearGroup.coe_neg]

def chiralSwapRep (R : HolomorphicLorentzRep ι) : HolomorphicLorentzRep ι where
  σ :=
    { toFun := fun p => R.σ (p.2, p.1)
      map_one' := R.σ.map_one
      map_mul' := fun p q => R.σ.map_mul (p.2, p.1) (q.2, q.1) }
  polynomial i j := IsPoly.swap (R.polynomial i j)

lemma chiralSwapRep_spinParity {R : HolomorphicLorentzRep ι} {ε : ℂ}
    (hε : R.HasSpinParity ε) :
    (chiralSwapRep R).HasSpinParity ε :=
  hε

@[simp]
lemma chiralSwapRep_leftWeylRep : chiralSwapRep leftWeylRep = rightWeylRep := rfl

@[simp]
lemma chiralSwapRep_rightWeylRep : chiralSwapRep rightWeylRep = leftWeylRep := rfl

def directSumRep {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (R₁ : HolomorphicLorentzRep ι₁) (R₂ : HolomorphicLorentzRep ι₂) :
    HolomorphicLorentzRep (ι₁ ⊕ ι₂) where
  σ :=
    { toFun := fun p => Matrix.fromBlocks (R₁.σ p) 0 0 (R₂.σ p)
      map_one' := by simp [Matrix.fromBlocks_one]
      map_mul' := fun p q => by simp [Matrix.fromBlocks_multiply] }
  polynomial i j := by
    rcases i with i₁ | i₂ <;> rcases j with j₁ | j₂
    · exact R₁.polynomial i₁ j₁
    · exact IsPoly.const 0
    · exact IsPoly.const 0
    · exact R₂.polynomial i₂ j₂

lemma directSumRep_spinParity {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁]
    [Fintype ι₂] [DecidableEq ι₂]
    {R₁ : HolomorphicLorentzRep ι₁} {R₂ : HolomorphicLorentzRep ι₂} {ε : ℂ}
    (h₁ : R₁.HasSpinParity ε) (h₂ : R₂.HasSpinParity ε) :
    (directSumRep R₁ R₂).HasSpinParity ε := by
  refine ⟨?_, h₁.2⟩
  change Matrix.fromBlocks (R₁.σ (-1, -1)) 0 0 (R₂.σ (-1, -1)) =
    ε • (1 : Matrix (ι₁ ⊕ ι₂) (ι₁ ⊕ ι₂) ℂ)
  rw [h₁.1, h₂.1, ← Matrix.fromBlocks_one]
  ext (i₁ | i₂) (j₁ | j₂) <;> simp [Matrix.one_apply]

def diracRep : HolomorphicLorentzRep (Fin 2 ⊕ Fin 2) :=
  directSumRep leftWeylRep rightWeylRep

lemma diracRep_spinParity : diracRep.HasSpinParity (-1) :=
  directSumRep_spinParity leftWeylRep_spinParity rightWeylRep_spinParity

def tensorProdRep {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁] [Fintype ι₂] [DecidableEq ι₂]
    (R₁ : HolomorphicLorentzRep ι₁) (R₂ : HolomorphicLorentzRep ι₂) :
    HolomorphicLorentzRep (ι₁ × ι₂) where
  σ :=
    { toFun := fun p i j => R₁.σ p i.1 j.1 * R₂.σ p i.2 j.2
      map_one' := by
        ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
        by_cases h1 : i₁ = j₁ <;> by_cases h2 : i₂ = j₂ <;>
          simp [h1, h2, Matrix.one_apply, Prod.ext_iff]
      map_mul' := fun p q => by
        ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
        dsimp
        rw [R₁.σ.map_mul, R₂.σ.map_mul, Matrix.mul_apply, Matrix.mul_apply, Matrix.mul_apply,
          Fintype.sum_prod_type, Finset.sum_mul]
        simp_rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun k₁ _ => Finset.sum_congr rfl (fun k₂ _ => ?_))
        ring }
  polynomial i j := IsPoly.mul (R₁.polynomial i.1 j.1) (R₂.polynomial i.2 j.2)

lemma tensorProdRep_spinParity {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁]
    [Fintype ι₂] [DecidableEq ι₂]
    {R₁ : HolomorphicLorentzRep ι₁} {R₂ : HolomorphicLorentzRep ι₂} {ε₁ ε₂ : ℂ}
    (h₁ : R₁.HasSpinParity ε₁) (h₂ : R₂.HasSpinParity ε₂) :
    (tensorProdRep R₁ R₂).HasSpinParity (ε₁ * ε₂) := by
  refine ⟨?_, ?_⟩
  · ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    change R₁.σ (-1, -1) i₁ j₁ * R₂.σ (-1, -1) i₂ j₂ =
      ((ε₁ * ε₂) • (1 : Matrix (ι₁ × ι₂) (ι₁ × ι₂) ℂ)) (i₁, i₂) (j₁, j₂)
    rw [h₁.1, h₂.1]
    simp only [Matrix.smul_apply, Matrix.one_apply, Prod.mk.injEq, smul_eq_mul]
    by_cases h1 : i₁ = j₁ <;> by_cases h2 : i₂ = j₂ <;> simp [h1, h2]
  · rcases h₁.2 with rfl | rfl <;> rcases h₂.2 with rfl | rfl <;> simp

def multiSpinorRep (m : ℕ) (R : HolomorphicLorentzRep ι) :
    HolomorphicLorentzRep (Fin m → ι) where
  σ :=
    { toFun := fun p α β => ∏ k : Fin m, R.σ p (α k) (β k)
      map_one' := by
        ext α β
        rw [R.σ.map_one]
        by_cases h : α = β
        · subst h
          simp
        · rw [Matrix.one_apply_ne h]
          obtain ⟨k, hk⟩ : ∃ k, α k ≠ β k := by
            by_contra hc
            push Not at hc
            exact h (funext hc)
          exact Finset.prod_eq_zero (Finset.mem_univ k) (Matrix.one_apply_ne hk)
      map_mul' := fun p q => by
        ext α β
        rw [Matrix.mul_apply]
        simp_rw [R.σ.map_mul, Matrix.mul_apply]
        rw [Fintype.prod_sum]
        refine Finset.sum_congr rfl (fun γ _ => ?_)
        rw [Finset.prod_mul_distrib] }
  polynomial α β :=
    IsPoly.prod Finset.univ (fun k p => R.σ p (α k) (β k)) (fun k _ => R.polynomial (α k) (β k))

lemma neg_one_pow_eq_one_or_neg_one (m : ℕ) :
    (-1 : ℂ) ^ m = 1 ∨ (-1 : ℂ) ^ m = -1 := by
  rcases Nat.even_or_odd m with hm | hm
  · exact Or.inl (Even.neg_one_pow hm)
  · exact Or.inr (Odd.neg_one_pow hm)

lemma spinParity_pow {ε : ℂ} (hε : ε = 1 ∨ ε = -1) (m : ℕ) :
    ε ^ m = 1 ∨ ε ^ m = -1 := by
  rcases hε with rfl | rfl
  · exact Or.inl (one_pow m)
  · exact neg_one_pow_eq_one_or_neg_one m

lemma multiSpinorRep_spinParity (m : ℕ) {R : HolomorphicLorentzRep ι} {ε : ℂ}
    (hε : R.HasSpinParity ε) :
    (multiSpinorRep m R).HasSpinParity (ε ^ m) := by
  refine ⟨?_, spinParity_pow hε.2 m⟩
  ext α β
  change (∏ k : Fin m, R.σ (-1, -1) (α k) (β k)) =
    (ε ^ m) * (1 : Matrix (Fin m → ι) (Fin m → ι) ℂ) α β
  rw [prod_spinParity R ε hε m α β]
  by_cases h : α = β <;> simp [h, Matrix.one_apply]

def spinorTensorRep (m₁ m₂ : ℕ) :
    HolomorphicLorentzRep ((Fin m₁ → Fin 2) × (Fin m₂ → Fin 2)) :=
  tensorProdRep (multiSpinorRep m₁ leftWeylRep) (multiSpinorRep m₂ rightWeylRep)

lemma spinorTensorRep_spinParity (m₁ m₂ : ℕ) :
    (spinorTensorRep m₁ m₂).HasSpinParity ((-1 : ℂ) ^ (m₁ + m₂)) := by
  rw [pow_add]
  exact tensorProdRep_spinParity
    (multiSpinorRep_spinParity m₁ leftWeylRep_spinParity)
    (multiSpinorRep_spinParity m₂ rightWeylRep_spinParity)

open Geometry.MatrixAnalysis

def HolomorphicLorentzRep.HasRealConj (R : HolomorphicLorentzRep ι) : Prop :=
  ∀ A B : SL2C, (R.σ (sl2c_conj A, sl2c_conj B)).map star = R.σ (A, B)

lemma leftWeylRep_hasRealConj : leftWeylRep.HasRealConj := by
  intro A B
  ext i j
  change star (star (A.1 i j)) = A.1 i j
  exact star_star _

lemma rightWeylRep_hasRealConj : rightWeylRep.HasRealConj := by
  intro A B
  ext i j
  change star (star (B.1 i j)) = B.1 i j
  exact star_star _

lemma chiralSwapRep_hasRealConj {R : HolomorphicLorentzRep ι} (hR : R.HasRealConj) :
    (chiralSwapRep R).HasRealConj :=
  fun A B => hR B A

lemma tensorProdRep_hasRealConj {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁]
    [Fintype ι₂] [DecidableEq ι₂]
    {R₁ : HolomorphicLorentzRep ι₁} {R₂ : HolomorphicLorentzRep ι₂}
    (h₁ : R₁.HasRealConj) (h₂ : R₂.HasRealConj) :
    (tensorProdRep R₁ R₂).HasRealConj := by
  intro A B
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  change star (R₁.σ (sl2c_conj A, sl2c_conj B) i₁ j₁ *
    R₂.σ (sl2c_conj A, sl2c_conj B) i₂ j₂) =
    R₁.σ (A, B) i₁ j₁ * R₂.σ (A, B) i₂ j₂
  have h1' : star (R₁.σ (sl2c_conj A, sl2c_conj B) i₁ j₁) = R₁.σ (A, B) i₁ j₁ :=
    congrFun (congrFun (h₁ A B) i₁) j₁
  have h2' : star (R₂.σ (sl2c_conj A, sl2c_conj B) i₂ j₂) = R₂.σ (A, B) i₂ j₂ :=
    congrFun (congrFun (h₂ A B) i₂) j₂
  rw [star_mul', h1', h2']

lemma multiSpinorRep_hasRealConj (m : ℕ) {R : HolomorphicLorentzRep ι} (hR : R.HasRealConj) :
    (multiSpinorRep m R).HasRealConj := by
  intro A B
  ext α β
  change (starRingEnd ℂ) (∏ k : Fin m, R.σ (sl2c_conj A, sl2c_conj B) (α k) (β k)) =
    ∏ k : Fin m, R.σ (A, B) (α k) (β k)
  rw [map_prod]
  refine Finset.prod_congr rfl (fun k _ => ?_)
  exact congrFun (congrFun (hR A B) (α k)) (β k)

lemma spinorTensorRep_hasRealConj (m₁ m₂ : ℕ) :
    (spinorTensorRep m₁ m₂).HasRealConj :=
  tensorProdRep_hasRealConj
    (multiSpinorRep_hasRealConj m₁ leftWeylRep_hasRealConj)
    (multiSpinorRep_hasRealConj m₂ rightWeylRep_hasRealConj)

def trivialStarStructure : StarStructure trivialRep where
  C := 1
  involutive := by ext i j; simp
  intertwine A B := by ext i j; simp [trivialRep]

def stdStarStructure : StarStructure stdRep where
  C := 1
  involutive := by
    have h1 : (1 : Matrix (Fin 4) (Fin 4) ℂ).map star = 1 := by
      ext i j; fin_cases i <;> fin_cases j <;> simp
    rw [h1, mul_one]
  intertwine A B := by
    have h_conj : (stdRep.σ (sl2c_conj B, sl2c_conj A)).map star = stdRep.σ (A, B) := by
      change Matrix.map (spinorPhi (sl2c_conj B, sl2c_conj A)).val.val star =
        (spinorPhi (A, B)).val.val
      rw [← spinorPhi_conj A B]
      ext i j
      simp [Matrix.map_apply]
    rw [one_mul, h_conj, mul_one]

def directSumStarStructure {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁]
    [Fintype ι₂] [DecidableEq ι₂]
    {R₁ : HolomorphicLorentzRep ι₁} {R₂ : HolomorphicLorentzRep ι₂}
    (S₁ : StarStructure R₁) (S₂ : StarStructure R₂) :
    StarStructure (directSumRep R₁ R₂) where
  C := Matrix.fromBlocks S₁.C 0 0 S₂.C
  involutive := by
    have h_star : (Matrix.fromBlocks S₁.C (0 : Matrix ι₁ ι₂ ℂ) 0 S₂.C).map star =
        Matrix.fromBlocks (S₁.C.map star) 0 0 (S₂.C.map star) := by
      ext (i₁ | i₂) (j₁ | j₂) <;> simp [Matrix.fromBlocks]
    rw [h_star, Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      S₁.involutive, S₂.involutive, Matrix.fromBlocks_one]
  intertwine A B := by
    change Matrix.fromBlocks S₁.C 0 0 S₂.C *
        Matrix.fromBlocks (R₁.σ (A, B)) 0 0 (R₂.σ (A, B)) =
      (Matrix.fromBlocks (R₁.σ (sl2c_conj B, sl2c_conj A)) 0 0
        (R₂.σ (sl2c_conj B, sl2c_conj A))).map star *
        Matrix.fromBlocks S₁.C 0 0 S₂.C
    have h_star : (Matrix.fromBlocks (R₁.σ (sl2c_conj B, sl2c_conj A)) (0 : Matrix ι₁ ι₂ ℂ) 0
        (R₂.σ (sl2c_conj B, sl2c_conj A))).map star =
        Matrix.fromBlocks ((R₁.σ (sl2c_conj B, sl2c_conj A)).map star) 0 0
          ((R₂.σ (sl2c_conj B, sl2c_conj A)).map star) := by
      ext (i₁ | i₂) (j₁ | j₂) <;> simp [Matrix.fromBlocks]
    rw [h_star, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      S₁.intertwine A B, S₂.intertwine A B]

def tensorProdStarStructure {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁]
    [Fintype ι₂] [DecidableEq ι₂]
    {R₁ : HolomorphicLorentzRep ι₁} {R₂ : HolomorphicLorentzRep ι₂}
    (S₁ : StarStructure R₁) (S₂ : StarStructure R₂) :
    StarStructure (tensorProdRep R₁ R₂) where
  C i j := S₁.C i.1 j.1 * S₂.C i.2 j.2
  involutive := by
    ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    simp only [Matrix.mul_apply, Matrix.map_apply, Fintype.sum_prod_type, star_mul']
    have h_Prod :
        (∑ x : ι₁, ∑ x_1 : ι₂,
          S₁.C i₁ x * S₂.C i₂ x_1 * (star (S₁.C x j₁) * star (S₂.C x_1 j₂))) =
        (∑ x : ι₁, S₁.C i₁ x * star (S₁.C x j₁)) *
          (∑ x_1 : ι₂, S₂.C i₂ x_1 * star (S₂.C x_1 j₂)) := by
      rw [Finset.sum_mul]
      simp_rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun x₁ _ => Finset.sum_congr rfl (fun x₂ _ => ?_))
      ring
    rw [h_Prod]
    have h1 := congrFun (congrFun S₁.involutive i₁) j₁
    have h2 := congrFun (congrFun S₂.involutive i₂) j₂
    simp only [Matrix.mul_apply, Matrix.map_apply] at h1 h2
    rw [h1, h2]
    by_cases h1' : i₁ = j₁ <;> by_cases h2' : i₂ = j₂ <;>
      simp [h1', h2', Matrix.one_apply, Prod.ext_iff]
  intertwine A B := by
    ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
    simp only [Matrix.mul_apply, Matrix.map_apply, Fintype.sum_prod_type]
    have h_lhs :
        (∑ x : ι₁, ∑ y : ι₂, S₁.C i₁ x * S₂.C i₂ y *
          ((tensorProdRep R₁ R₂).σ (A, B) (x, y) (j₁, j₂))) =
        (∑ x : ι₁, S₁.C i₁ x * R₁.σ (A, B) x j₁) *
          (∑ y : ι₂, S₂.C i₂ y * R₂.σ (A, B) y j₂) := by
      rw [Finset.sum_mul]
      simp_rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
      change S₁.C i₁ x * S₂.C i₂ y * (R₁.σ (A, B) x j₁ * R₂.σ (A, B) y j₂) = _
      ring
    have h_rhs :
        (∑ x : ι₁, ∑ y : ι₂,
          star ((tensorProdRep R₁ R₂).σ (sl2c_conj B, sl2c_conj A) (i₁, i₂) (x, y)) *
            (S₁.C x j₁ * S₂.C y j₂)) =
        (∑ x : ι₁, star (R₁.σ (sl2c_conj B, sl2c_conj A) i₁ x) * S₁.C x j₁) *
          (∑ y : ι₂, star (R₂.σ (sl2c_conj B, sl2c_conj A) i₂ y) * S₂.C y j₂) := by
      rw [Finset.sum_mul]
      simp_rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
      change star (R₁.σ (sl2c_conj B, sl2c_conj A) i₁ x *
        R₂.σ (sl2c_conj B, sl2c_conj A) i₂ y) * (S₁.C x j₁ * S₂.C y j₂) = _
      rw [star_mul']
      ring
    rw [h_lhs, h_rhs]
    have h1 := congrFun (congrFun (S₁.intertwine A B) i₁) j₁
    have h2 := congrFun (congrFun (S₂.intertwine A B) i₂) j₂
    simp only [Matrix.mul_apply, Matrix.map_apply] at h1 h2
    rw [h1, h2]

def chiralDoubleStarStructure (R : HolomorphicLorentzRep ι) (hR : R.HasRealConj) :
    StarStructure (directSumRep R (chiralSwapRep R)) where
  C := Matrix.fromBlocks (0 : Matrix ι ι ℂ) (1 : Matrix ι ι ℂ)
    (1 : Matrix ι ι ℂ) (0 : Matrix ι ι ℂ)
  involutive := by
    have h_star : (Matrix.fromBlocks (0 : Matrix ι ι ℂ) (1 : Matrix ι ι ℂ)
        (1 : Matrix ι ι ℂ) (0 : Matrix ι ι ℂ)).map star =
        Matrix.fromBlocks (0 : Matrix ι ι ℂ) (1 : Matrix ι ι ℂ)
          (1 : Matrix ι ι ℂ) (0 : Matrix ι ι ℂ) := by
      ext (i₁ | i₂) (j₁ | j₂)
      · simp
      · by_cases hij : i₁ = j₂ <;> simp [hij]
      · by_cases hij : i₂ = j₁ <;> simp [hij]
      · simp
    rw [h_star, Matrix.fromBlocks_multiply]
    simp [Matrix.fromBlocks_one]
  intertwine A B := by
    change Matrix.fromBlocks (0 : Matrix ι ι ℂ) (1 : Matrix ι ι ℂ)
        (1 : Matrix ι ι ℂ) (0 : Matrix ι ι ℂ) *
        Matrix.fromBlocks (R.σ (A, B)) 0 0 (R.σ (B, A)) =
      (Matrix.fromBlocks (R.σ (sl2c_conj B, sl2c_conj A)) 0 0
        (R.σ (sl2c_conj A, sl2c_conj B))).map star *
        Matrix.fromBlocks (0 : Matrix ι ι ℂ) (1 : Matrix ι ι ℂ)
          (1 : Matrix ι ι ℂ) (0 : Matrix ι ι ℂ)
    have h_star : (Matrix.fromBlocks (R.σ (sl2c_conj B, sl2c_conj A)) (0 : Matrix ι ι ℂ) 0
        (R.σ (sl2c_conj A, sl2c_conj B))).map star =
        Matrix.fromBlocks (R.σ (B, A)) 0 0 (R.σ (A, B)) := by
      ext (i₁ | i₂) (j₁ | j₂)
      · exact congrFun (congrFun (hR B A) i₁) j₁
      · simp
      · simp
      · exact congrFun (congrFun (hR A B) i₂) j₂
    rw [h_star, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp

def diracStarStructure : StarStructure diracRep :=
  chiralDoubleStarStructure leftWeylRep leftWeylRep_hasRealConj

def spinorTensorBispinorStarStructure (m₁ m₂ : ℕ) :
    StarStructure (directSumRep (spinorTensorRep m₁ m₂) (chiralSwapRep (spinorTensorRep m₁ m₂))) :=
  chiralDoubleStarStructure (spinorTensorRep m₁ m₂) (spinorTensorRep_hasRealConj m₁ m₂)

def spinorTensorDiagonalStarStructure (m : ℕ) : StarStructure (spinorTensorRep m m) where
  C i j := if i.2 = j.1 ∧ i.1 = j.2 then 1 else 0
  involutive := by
    ext ⟨α₁, α₂⟩ ⟨β₁, β₂⟩
    simp only [Matrix.mul_apply, Matrix.map_apply, Fintype.sum_prod_type]
    have h_sum : (∑ x : Fin m → Fin 2, ∑ y : Fin m → Fin 2,
        (if α₂ = x ∧ α₁ = y then (1 : ℂ) else 0) *
          star (if y = β₁ ∧ x = β₂ then (1 : ℂ) else 0)) =
        if α₂ = β₂ ∧ α₁ = β₁ then 1 else 0 := by
      simp [apply_ite star, star_one, star_zero, ite_and]
    rw [h_sum]
    by_cases h1 : α₁ = β₁ <;> by_cases h2 : α₂ = β₂ <;>
      simp [h1, h2, Matrix.one_apply, Prod.ext_iff]
  intertwine A B := by
    ext ⟨α₁, α₂⟩ ⟨β₁, β₂⟩
    simp only [Matrix.mul_apply, Matrix.map_apply, Fintype.sum_prod_type]
    have h_lhs : (∑ x : Fin m → Fin 2, ∑ y : Fin m → Fin 2,
        (if α₂ = x ∧ α₁ = y then (1 : ℂ) else 0) *
          (spinorTensorRep m m).σ (A, B) (x, y) (β₁, β₂)) =
        (spinorTensorRep m m).σ (A, B) (α₂, α₁) (β₁, β₂) := by
      simp [ite_and]
    have h_rhs : (∑ x : Fin m → Fin 2, ∑ y : Fin m → Fin 2,
        star ((spinorTensorRep m m).σ (sl2c_conj B, sl2c_conj A) (α₁, α₂) (x, y)) *
          (if y = β₁ ∧ x = β₂ then (1 : ℂ) else 0)) =
        star ((spinorTensorRep m m).σ (sl2c_conj B, sl2c_conj A) (α₁, α₂) (β₂, β₁)) := by
      simp [ite_and]
    rw [h_lhs, h_rhs]
    change (∏ k : Fin m, A.1 (α₂ k) (β₁ k)) * (∏ k : Fin m, B.1 (α₁ k) (β₂ k)) =
      star ((∏ k : Fin m, (sl2c_conj B).1 (α₁ k) (β₂ k)) *
        (∏ k : Fin m, (sl2c_conj A).1 (α₂ k) (β₁ k)))
    rw [star_mul']
    have hB : star (∏ k : Fin m, (sl2c_conj B).1 (α₁ k) (β₂ k)) =
        ∏ k : Fin m, B.1 (α₁ k) (β₂ k) :=
      congrFun (congrFun (multiSpinorRep_hasRealConj m leftWeylRep_hasRealConj B A) α₁) β₂
    have hA : star (∏ k : Fin m, (sl2c_conj A).1 (α₂ k) (β₁ k)) =
        ∏ k : Fin m, A.1 (α₂ k) (β₁ k) :=
      congrFun (congrFun (multiSpinorRep_hasRealConj m rightWeylRep_hasRealConj B A) α₂) β₁
    rw [hB, hA, mul_comm]

abbrev ScalarOSReconstructedWightman (η : ℂ) (𝒮 : SchwingerFamily Unit) :=
  OSReconstructedWightman trivialRep trivialStarStructure η 𝒮

abbrev VectorOSReconstructedWightman (η : ℂ) (𝒮 : SchwingerFamily (Fin 4)) :=
  OSReconstructedWightman stdRep stdStarStructure η 𝒮

abbrev DiracOSReconstructedWightman (η : ℂ) (𝒮 : SchwingerFamily (Fin 2 ⊕ Fin 2)) :=
  OSReconstructedWightman diracRep diracStarStructure η 𝒮

abbrev SpinorTensorBispinorOSReconstructedWightman (m₁ m₂ : ℕ) (η : ℂ)
    (𝒮 : SchwingerFamily (((Fin m₁ → Fin 2) × (Fin m₂ → Fin 2)) ⊕
      ((Fin m₁ → Fin 2) × (Fin m₂ → Fin 2)))) :=
  OSReconstructedWightman
    (directSumRep (spinorTensorRep m₁ m₂) (chiralSwapRep (spinorTensorRep m₁ m₂)))
    (spinorTensorBispinorStarStructure m₁ m₂) η 𝒮

theorem spin_statistics_rightWeylRep (W : WightmanFamily (Fin 2)) {η : ℂ}
    (E : TubeExtension W)
    (h_tloc : TubeWeakLocality η E)
    (h_exch : TwoPointSpinExchange (-1) E)
    (h_nondeg : ∃ (α : Fin 2 → Fin 2) (z : Fin 2 → Fin 4 → ℂ),
      z ∈ forward_tube_n 2 ∧ E.H 2 (α ∘ Fin.rev) z ≠ 0) :
    η = -1 :=
  spin_statistics_theorem_tube rightWeylRep W E rightWeylRep_spinParity h_tloc h_exch h_nondeg

theorem spin_statistics_diracRep (W : WightmanFamily (Fin 2 ⊕ Fin 2)) {η : ℂ}
    (E : TubeExtension W)
    (h_tloc : TubeWeakLocality η E)
    (h_exch : TwoPointSpinExchange (-1) E)
    (h_nondeg : ∃ (α : Fin 2 → Fin 2 ⊕ Fin 2) (z : Fin 2 → Fin 4 → ℂ),
      z ∈ forward_tube_n 2 ∧ E.H 2 (α ∘ Fin.rev) z ≠ 0) :
    η = -1 :=
  spin_statistics_theorem_tube diracRep W E diracRep_spinParity h_tloc h_exch h_nondeg

theorem scalar_os_spin_statistics {η : ℂ} {𝒮 : SchwingerFamily Unit}
    (P : ScalarOSReconstructedWightman η 𝒮)
    (h_exch : TwoPointSpinExchange 1 P.E)
    (h_nondeg : ∃ (α : Fin 2 → Unit) (f : SchwartzMap (Fin 2 → Fin 4 → ℝ) ℂ), P.W 2 α f ≠ 0) :
    η = 1 :=
  P.spin_statistics_of_twoPoint_ne_zero trivialRep_spinParity h_exch h_nondeg

theorem vector_os_spin_statistics {η : ℂ} {𝒮 : SchwingerFamily (Fin 4)}
    (P : VectorOSReconstructedWightman η 𝒮)
    (h_exch : TwoPointSpinExchange 1 P.E)
    (h_nondeg : ∃ (α : Fin 2 → Fin 4) (f : SchwartzMap (Fin 2 → Fin 4 → ℝ) ℂ), P.W 2 α f ≠ 0) :
    η = 1 :=
  P.spin_statistics_of_twoPoint_ne_zero stdRep_spinParity h_exch h_nondeg

theorem dirac_os_schwinger_eq_zero_of_odd {η : ℂ} {𝒮 : SchwingerFamily (Fin 2 ⊕ Fin 2)}
    (P : DiracOSReconstructedWightman η 𝒮)
    (n : ℕ) (hn : Odd n) (x : Fin n → Fin 4 → ℝ) (hx : x ∈ orderedEuclidN n)
    (α : Fin n → Fin 2 ⊕ Fin 2) :
    𝒮 n α x = 0 :=
  P.schwinger_eq_zero_of_odd_fermion diracRep_spinParity n hn x hx α

theorem dirac_os_spin_statistics_from_schwinger {η : ℂ} {𝒮 : SchwingerFamily (Fin 2 ⊕ Fin 2)}
    (P : DiracOSReconstructedWightman η 𝒮)
    (h_exch : TwoPointSpinExchange (-1) P.E)
    (h_nondeg : ∃ (α : Fin 2 → Fin 2 ⊕ Fin 2) (x : Fin 2 → Fin 4 → ℝ),
      x ∈ orderedEuclidN 2 ∧ 𝒮 2 (α ∘ Fin.rev) x ≠ 0) :
    η = -1 :=
  P.spin_statistics_from_schwinger diracRep_spinParity h_exch h_nondeg

theorem dirac_os_spin_statistics_of_twoPoint_ne_zero {η : ℂ} {𝒮 : SchwingerFamily (Fin 2 ⊕ Fin 2)}
    (P : DiracOSReconstructedWightman η 𝒮)
    (h_exch : TwoPointSpinExchange (-1) P.E)
    (h_nondeg : ∃ (α : Fin 2 → Fin 2 ⊕ Fin 2)
      (f : SchwartzMap (Fin 2 → Fin 4 → ℝ) ℂ), P.W 2 α f ≠ 0) :
    η = -1 :=
  P.spin_statistics_of_twoPoint_ne_zero diracRep_spinParity h_exch h_nondeg

theorem spinorTensorRep_schwinger_spin_parity_selection (m₁ m₂ : ℕ)
    (W : WightmanFamily ((Fin m₁ → Fin 2) × (Fin m₂ → Fin 2)))
    (E : TubeExtension W) (hcov : TubeCovariant (spinorTensorRep m₁ m₂) E)
    (n : ℕ) (x : Fin n → Fin 4 → ℝ) (hx : x ∈ orderedEuclidN n)
    (α : Fin n → (Fin m₁ → Fin 2) × (Fin m₂ → Fin 2)) :
    schwingerFromTube E n α x = ((-1 : ℂ) ^ (m₁ + m₂)) ^ n * schwingerFromTube E n α x :=
  schwingerFromTube_spin_parity_selection (spinorTensorRep m₁ m₂) W E hcov
    (spinorTensorRep_spinParity m₁ m₂) n x hx α

theorem spinorTensorRep_schwinger_eq_zero_of_odd (m₁ m₂ : ℕ) (hm : Odd (m₁ + m₂))
    (W : WightmanFamily ((Fin m₁ → Fin 2) × (Fin m₂ → Fin 2)))
    (E : TubeExtension W) (hcov : TubeCovariant (spinorTensorRep m₁ m₂) E)
    (n : ℕ) (hn : Odd n) (x : Fin n → Fin 4 → ℝ) (hx : x ∈ orderedEuclidN n)
    (α : Fin n → (Fin m₁ → Fin 2) × (Fin m₂ → Fin 2)) :
    schwingerFromTube E n α x = 0 := by
  have hε : (spinorTensorRep m₁ m₂).HasSpinParity (-1) := by
    have h := spinorTensorRep_spinParity m₁ m₂
    rwa [Odd.neg_one_pow hm] at h
  exact schwingerFromTube_eq_zero_of_odd_fermion (spinorTensorRep m₁ m₂) W E hcov
    hε n hn x hx α

theorem spinorTensorRep_spin_statistics (m₁ m₂ : ℕ)
    (W : WightmanFamily ((Fin m₁ → Fin 2) × (Fin m₂ → Fin 2)))
    (E : TubeExtension W) {η : ℂ}
    (hloc : TubeWeakLocality η E)
    (h_exch : TwoPointSpinExchange ((-1 : ℂ) ^ (m₁ + m₂)) E)
    (h_nondeg : ∃ (α : Fin 2 → (Fin m₁ → Fin 2) × (Fin m₂ → Fin 2))
      (f : SchwartzMap (Fin 2 → Fin 4 → ℝ) ℂ), W 2 α f ≠ 0) :
    η = (-1 : ℂ) ^ (m₁ + m₂) :=
  spin_statistics_of_twoPoint_wightman_ne_zero (spinorTensorRep m₁ m₂) W E
    (spinorTensorRep_spinParity m₁ m₂) hloc h_exch h_nondeg

theorem spinorTensorBispinor_os_spin_statistics (m₁ m₂ : ℕ) {η : ℂ}
    {𝒮 : SchwingerFamily (((Fin m₁ → Fin 2) × (Fin m₂ → Fin 2)) ⊕
      ((Fin m₁ → Fin 2) × (Fin m₂ → Fin 2)))}
    (P : SpinorTensorBispinorOSReconstructedWightman m₁ m₂ η 𝒮)
    (h_exch : TwoPointSpinExchange ((-1 : ℂ) ^ (m₁ + m₂)) P.E)
    (h_nondeg : ∃ (α : Fin 2 → ((Fin m₁ → Fin 2) × (Fin m₂ → Fin 2)) ⊕
      ((Fin m₁ → Fin 2) × (Fin m₂ → Fin 2)))
      (f : SchwartzMap (Fin 2 → Fin 4 → ℝ) ℂ), P.W 2 α f ≠ 0) :
    η = (-1 : ℂ) ^ (m₁ + m₂) :=
  P.spin_statistics_of_twoPoint_ne_zero
    (directSumRep_spinParity (spinorTensorRep_spinParity m₁ m₂)
      (chiralSwapRep_spinParity (spinorTensorRep_spinParity m₁ m₂)))
    h_exch h_nondeg

omit [Fintype ι] [DecidableEq ι] in
lemma neg_rev_two_eq_add_neg_sum (z : Fin 2 → Fin 4 → ℂ) :
    -(z ∘ Fin.rev) = fun i => z i + (-(z 0 + z 1)) := by
  ext i μ
  fin_cases i <;>
  · change -(z (Fin.rev _) μ) = z _ μ + -(z 0 μ + z 1 μ)
    dsimp [Fin.rev]
    ring

omit [Fintype ι] [DecidableEq ι] in
lemma euclid_neg_rev_two_eq_add_neg_sum (x : Fin 2 → Fin 4 → ℝ) :
    -(x ∘ Fin.rev) = fun i => x i + (-(x 0 + x 1)) := by
  ext i μ
  fin_cases i <;>
  · change -(x (Fin.rev _) μ) = x _ μ + -(x 0 μ + x 1 μ)
    dsimp [Fin.rev]
    ring

omit [Fintype ι] [DecidableEq ι] in
def complexNegRevCLM (n : ℕ) : (Fin n → Fin 4 → ℂ) →L[ℂ] (Fin n → Fin 4 → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => -(z ∘ Fin.rev)
      map_add' := fun z₁ z₂ => by ext i μ; simp [add_comm]
      map_smul' := fun c z => by ext i μ; simp }

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma complexNegRevCLM_apply (n : ℕ) (z : Fin n → Fin 4 → ℂ) :
    complexNegRevCLM n z = -(z ∘ Fin.rev) := rfl

omit [Fintype ι] [DecidableEq ι] in
lemma analyticOn_forward_tube_neg_rev (n : ℕ) {f : (Fin n → Fin 4 → ℂ) → ℂ}
    (hf : AnalyticOn ℂ f (forward_tube_n n)) :
    AnalyticOn ℂ (fun z => f (-(z ∘ Fin.rev))) (forward_tube_n n) :=
  hf.comp ((complexNegRevCLM n).analyticOn (forward_tube_n n))
    (fun z hz => neg_rev_mem_forward_tube_n n z hz)

omit [Fintype ι] [DecidableEq ι] in
theorem tubeTranslationInvariant_neg_rev_two {W : WightmanFamily ι}
    (E : TubeExtension W) (htrans : TubeTranslationInvariant E)
    (α : Fin 2 → ι) (z : Fin 2 → Fin 4 → ℂ) (hz : z ∈ forward_tube_n 2) :
    E.H 2 α (-(z ∘ Fin.rev)) = E.H 2 α z := by
  rw [neg_rev_two_eq_add_neg_sum z]
  exact htrans 2 α z (-(z 0 + z 1)) hz

omit [Fintype ι] [DecidableEq ι] in
theorem osTranslationInvariant_neg_rev_two {𝒮 : SchwingerFamily ι}
    (htrans : OSTranslationInvariant 𝒮)
    (α : Fin 2 → ι) (x : Fin 2 → Fin 4 → ℝ) (hx : x ∈ orderedEuclidN 2) :
    𝒮 2 α (-(x ∘ Fin.rev)) = 𝒮 2 α x := by
  rw [euclid_neg_rev_two_eq_add_neg_sum x]
  exact htrans 2 α x hx (-(x 0 + x 1))

omit [Fintype ι] [DecidableEq ι] in
theorem tube_neg_rev_two_eq_of_osTranslationInvariant {W : WightmanFamily ι}
    (E : TubeExtension W) (htrans : OSTranslationInvariant (schwingerFromTube E))
    (α : Fin 2 → ι) (z : Fin 2 → Fin 4 → ℂ) (hz : z ∈ forward_tube_n 2) :
    E.H 2 α (-(z ∘ Fin.rev)) = E.H 2 α z := by
  refine analyticOn_forward_tube_eq_of_wickEmbedN_eq 2
    (analyticOn_forward_tube_neg_rev 2 (E.analytic 2 α))
    (E.analytic 2 α) (fun x hx => ?_) hz
  change E.H 2 α (-(wickEmbedN 2 x ∘ Fin.rev)) = schwingerFromTube E 2 α x
  rw [← wickEmbedN_comp_rev, ← wickEmbedN_neg]
  exact osTranslationInvariant_neg_rev_two htrans α x hx

omit [Fintype ι] [DecidableEq ι] in
theorem twoPointSpinExchange_of_subsingleton [Subsingleton ι] {W : WightmanFamily ι}
    (E : TubeExtension W) (htrans : TubeTranslationInvariant E) :
    TwoPointSpinExchange 1 E := by
  intro α z hz
  rw [one_mul, Subsingleton.elim (α ∘ Fin.rev) α]
  exact tubeTranslationInvariant_neg_rev_two E htrans α z hz

omit [Fintype ι] [DecidableEq ι] in
theorem twoPointSpinExchange_of_subsingleton_osTranslationInvariant [Subsingleton ι]
    {W : WightmanFamily ι} (E : TubeExtension W)
    (htrans : OSTranslationInvariant (schwingerFromTube E)) :
    TwoPointSpinExchange 1 E := by
  intro α z hz
  rw [one_mul, Subsingleton.elim (α ∘ Fin.rev) α]
  exact tube_neg_rev_two_eq_of_osTranslationInvariant E htrans α z hz

theorem twoPointSpinExchange_trivialRep_of_translationInvariant {W : WightmanFamily Unit}
    (E : TubeExtension W) (htrans : TubeTranslationInvariant E) :
    TwoPointSpinExchange 1 E :=
  twoPointSpinExchange_of_subsingleton E htrans

theorem scalar_spin_statistics_unconditional (W : WightmanFamily Unit)
    (E : TubeExtension W) {η : ℂ}
    (htrans : TubeTranslationInvariant E)
    (hloc : TubeWeakLocality η E)
    (h_nondeg : ∃ (α : Fin 2 → Unit) (f : SchwartzMap (Fin 2 → Fin 4 → ℝ) ℂ), W 2 α f ≠ 0) :
    η = 1 :=
  spin_statistics_of_twoPoint_wightman_ne_zero trivialRep W E trivialRep_spinParity hloc
    (twoPointSpinExchange_trivialRep_of_translationInvariant E htrans) h_nondeg

omit [Fintype ι] [DecidableEq ι] in
theorem tube_twoPoint_diag_eq_eta_mul {W : WightmanFamily ι} {η : ℂ}
    (E : TubeExtension W) (htrans : TubeTranslationInvariant E)
    (hloc : TubeWeakLocality η E)
    (c : ι) (z : Fin 2 → Fin 4 → ℂ) (hz : z ∈ forward_tube_n 2) :
    E.H 2 (fun _ => c) z = η * E.H 2 (fun _ => c) z := by
  have h1 := tubeTranslationInvariant_neg_rev_two E htrans (fun _ => c) z hz
  have h2 := tubeWeakLocality_two hloc (fun _ => c) z hz
  exact h1.symm.trans h2

omit [Fintype ι] [DecidableEq ι] in
theorem fermion_tube_twoPoint_diag_eq_zero {W : WightmanFamily ι}
    (E : TubeExtension W) (htrans : TubeTranslationInvariant E)
    (hloc : TubeWeakLocality (-1) E)
    (c : ι) (z : Fin 2 → Fin 4 → ℂ) (hz : z ∈ forward_tube_n 2) :
    E.H 2 (fun _ => c) z = 0 := by
  have h := tube_twoPoint_diag_eq_eta_mul E htrans hloc c z hz
  linear_combination (1 / 2 : ℂ) * h

omit [Fintype ι] [DecidableEq ι] in
theorem fermion_schwinger_twoPoint_diag_eq_zero {W : WightmanFamily ι}
    (E : TubeExtension W) (htrans : TubeTranslationInvariant E)
    (hloc : TubeWeakLocality (-1) E)
    (c : ι) (x : Fin 2 → Fin 4 → ℝ) (hx : x ∈ orderedEuclidN 2) :
    schwingerFromTube E 2 (fun _ => c) x = 0 :=
  fermion_tube_twoPoint_diag_eq_zero E htrans hloc c
    (wickEmbedN 2 x) (wickEmbedN_mem_forward_tube_n 2 hx)

omit [Fintype ι] [DecidableEq ι] in
theorem fermion_wightman_twoPoint_diag_eq_zero {W : WightmanFamily ι}
    (E : TubeExtension W) (htrans : TubeTranslationInvariant E)
    (hloc : TubeWeakLocality (-1) E)
    (c : ι) (f : SchwartzMap (Fin 2 → Fin 4 → ℝ) ℂ) :
    W 2 (fun _ => c) f = 0 :=
  wightman_eq_zero_of_tube_eq_zero E 2 (fun _ => c)
    (fermion_tube_twoPoint_diag_eq_zero E htrans hloc c) f

def StarStructure.IsReal {R : HolomorphicLorentzRep ι} (S : StarStructure R) : Prop :=
  S.C.map star = S.C

lemma StarStructure.IsReal.mul_self_eq_one {R : HolomorphicLorentzRep ι}
    {S : StarStructure R} (hS : S.IsReal) :
    S.C * S.C = 1 := by
  have h := S.involutive
  rwa [hS] at h

lemma trivialStarStructure_isReal : trivialStarStructure.IsReal := by
  ext i j
  simp [trivialStarStructure]

lemma stdStarStructure_isReal : stdStarStructure.IsReal := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [stdStarStructure]

lemma directSumStarStructure_isReal {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁]
    [Fintype ι₂] [DecidableEq ι₂]
    {R₁ : HolomorphicLorentzRep ι₁} {R₂ : HolomorphicLorentzRep ι₂}
    {S₁ : StarStructure R₁} {S₂ : StarStructure R₂}
    (h₁ : S₁.IsReal) (h₂ : S₂.IsReal) :
    (directSumStarStructure S₁ S₂).IsReal := by
  change (Matrix.fromBlocks S₁.C (0 : Matrix ι₁ ι₂ ℂ) 0 S₂.C).map star =
    Matrix.fromBlocks S₁.C 0 0 S₂.C
  ext (i₁ | i₂) (j₁ | j₂)
  · exact congrFun (congrFun h₁ i₁) j₁
  · simp
  · simp
  · exact congrFun (congrFun h₂ i₂) j₂

lemma tensorProdStarStructure_isReal {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁]
    [Fintype ι₂] [DecidableEq ι₂]
    {R₁ : HolomorphicLorentzRep ι₁} {R₂ : HolomorphicLorentzRep ι₂}
    {S₁ : StarStructure R₁} {S₂ : StarStructure R₂}
    (h₁ : S₁.IsReal) (h₂ : S₂.IsReal) :
    (tensorProdStarStructure S₁ S₂).IsReal := by
  ext ⟨i₁, i₂⟩ ⟨j₁, j₂⟩
  change star (S₁.C i₁ j₁ * S₂.C i₂ j₂) = S₁.C i₁ j₁ * S₂.C i₂ j₂
  have h1' : star (S₁.C i₁ j₁) = S₁.C i₁ j₁ := congrFun (congrFun h₁ i₁) j₁
  have h2' : star (S₂.C i₂ j₂) = S₂.C i₂ j₂ := congrFun (congrFun h₂ i₂) j₂
  rw [star_mul', h1', h2']

lemma chiralDoubleStarStructure_isReal (R : HolomorphicLorentzRep ι) (hR : R.HasRealConj) :
    (chiralDoubleStarStructure R hR).IsReal := by
  change (Matrix.fromBlocks (0 : Matrix ι ι ℂ) (1 : Matrix ι ι ℂ)
    (1 : Matrix ι ι ℂ) (0 : Matrix ι ι ℂ)).map star =
    Matrix.fromBlocks (0 : Matrix ι ι ℂ) (1 : Matrix ι ι ℂ)
      (1 : Matrix ι ι ℂ) (0 : Matrix ι ι ℂ)
  ext (i₁ | i₂) (j₁ | j₂)
  · simp
  · by_cases hij : i₁ = j₂ <;> simp [hij]
  · by_cases hij : i₂ = j₁ <;> simp [hij]
  · simp

lemma diracStarStructure_isReal : diracStarStructure.IsReal :=
  chiralDoubleStarStructure_isReal leftWeylRep leftWeylRep_hasRealConj

lemma spinorTensorBispinorStarStructure_isReal (m₁ m₂ : ℕ) :
    (spinorTensorBispinorStarStructure m₁ m₂).IsReal :=
  chiralDoubleStarStructure_isReal (spinorTensorRep m₁ m₂) (spinorTensorRep_hasRealConj m₁ m₂)

lemma spinorTensorDiagonalStarStructure_isReal (m : ℕ) :
    (spinorTensorDiagonalStarStructure m).IsReal := by
  ext ⟨α₁, α₂⟩ ⟨β₁, β₂⟩
  change star (if α₂ = β₁ ∧ α₁ = β₂ then (1 : ℂ) else 0) =
    if α₂ = β₁ ∧ α₁ = β₂ then (1 : ℂ) else 0
  simp [apply_ite star]

def pctMatrix {R : HolomorphicLorentzRep ι} (S : StarStructure R) : Matrix ι ι ℂ :=
  S.C * R.σ (-1, 1)

lemma sigma_tp_map_star_of_hasRealConj {R : HolomorphicLorentzRep ι} (hR : R.HasRealConj) :
    (R.σ (1, -1)).map star = R.σ (1, -1) := by
  have h1 : sl2c_conj (1 : SL2C) = 1 := sl2c_conj_one
  have h2 : sl2c_conj (-1 : SL2C) = -1 := by
    apply Subtype.ext; ext i j; fin_cases i <;> fin_cases j <;> simp [sl2c_conj]
  have h := hR 1 (-1)
  rwa [h1, h2] at h

theorem starStructure_mul_sigma_pt_of_hasRealConj {R : HolomorphicLorentzRep ι}
    (S : StarStructure R) (hR : R.HasRealConj) :
    S.C * R.σ (-1, 1) = R.σ (1, -1) * S.C := by
  rw [starStructure_intertwine_pt S, sigma_tp_map_star_of_hasRealConj hR]

theorem pctMatrix_sq_eq_sigma_neg_one {R : HolomorphicLorentzRep ι}
    (S : StarStructure R) (hR : R.HasRealConj) (hS : S.IsReal) :
    pctMatrix S * pctMatrix S = R.σ (-1, -1) := by
  dsimp [pctMatrix]
  calc
    (S.C * R.σ (-1, 1)) * (S.C * R.σ (-1, 1))
      = (R.σ (1, -1) * S.C) * (S.C * R.σ (-1, 1)) := by
          rw [starStructure_mul_sigma_pt_of_hasRealConj S hR]
    _ = R.σ (1, -1) * (S.C * S.C) * R.σ (-1, 1) := by
          simp only [Matrix.mul_assoc]
    _ = R.σ (1, -1) * R.σ (-1, 1) := by
          rw [hS.mul_self_eq_one, Matrix.mul_one]
    _ = R.σ (-1, -1) := sigma_tp_mul_sigma_pt R

theorem pctMatrix_sq_eq_spinParity {R : HolomorphicLorentzRep ι}
    (S : StarStructure R) (hR : R.HasRealConj) (hS : S.IsReal)
    {ε : ℂ} (hε : R.HasSpinParity ε) :
    pctMatrix S * pctMatrix S = ε • (1 : Matrix ι ι ℂ) := by
  rw [pctMatrix_sq_eq_sigma_neg_one S hR hS, hε.1]

theorem dirac_pctMatrix_sq :
    pctMatrix diracStarStructure * pctMatrix diracStarStructure =
      (-1 : ℂ) • (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ) := by
  refine pctMatrix_sq_eq_spinParity diracStarStructure ?_ diracStarStructure_isReal
    diracRep_spinParity
  intro A B
  ext (i₁ | i₂) (j₁ | j₂)
  · exact congrFun (congrFun (leftWeylRep_hasRealConj A B) i₁) j₁
  · simp [diracRep, directSumRep]
  · simp [diracRep, directSumRep]
  · exact congrFun (congrFun (rightWeylRep_hasRealConj A B) i₂) j₂

theorem spinorTensorBispinor_pctMatrix_sq (m₁ m₂ : ℕ) :
    pctMatrix (spinorTensorBispinorStarStructure m₁ m₂) *
      pctMatrix (spinorTensorBispinorStarStructure m₁ m₂) =
      ((-1 : ℂ) ^ (m₁ + m₂)) •
        (1 : Matrix (((Fin m₁ → Fin 2) × (Fin m₂ → Fin 2)) ⊕
          ((Fin m₁ → Fin 2) × (Fin m₂ → Fin 2)))
          (((Fin m₁ → Fin 2) × (Fin m₂ → Fin 2)) ⊕
          ((Fin m₁ → Fin 2) × (Fin m₂ → Fin 2))) ℂ) := by
  refine pctMatrix_sq_eq_spinParity (spinorTensorBispinorStarStructure m₁ m₂) ?_
    (spinorTensorBispinorStarStructure_isReal m₁ m₂)
    (directSumRep_spinParity (spinorTensorRep_spinParity m₁ m₂)
      (chiralSwapRep_spinParity (spinorTensorRep_spinParity m₁ m₂)))
  intro A B
  ext (i₁ | i₂) (j₁ | j₂)
  · exact congrFun (congrFun (spinorTensorRep_hasRealConj m₁ m₂ A B) i₁) j₁
  · simp [directSumRep]
  · simp [directSumRep]
  · exact congrFun (congrFun
      (chiralSwapRep_hasRealConj (spinorTensorRep_hasRealConj m₁ m₂) A B) i₂) j₂

def TwoPointIndexExchange (ε : ℂ) {W : WightmanFamily ι} (E : TubeExtension W) : Prop :=
  ∀ (α : Fin 2 → ι) (z : Fin 2 → Fin 4 → ℂ),
    z ∈ forward_tube_n 2 →
    E.H 2 α z = ε * E.H 2 (α ∘ Fin.rev) z

def EuclidTwoPointIndexExchange (ε : ℂ) (𝒮 : SchwingerFamily ι) : Prop :=
  ∀ (α : Fin 2 → ι) (x : Fin 2 → Fin 4 → ℝ),
    x ∈ posOrderedEuclidN 2 →
    𝒮 2 α x = ε * 𝒮 2 (α ∘ Fin.rev) x

omit [Fintype ι] [DecidableEq ι] in
theorem twoPointSpinExchange_iff_twoPointIndexExchange {W : WightmanFamily ι}
    (E : TubeExtension W) (htrans : TubeTranslationInvariant E) (ε : ℂ) :
    TwoPointSpinExchange ε E ↔ TwoPointIndexExchange ε E := by
  constructor
  · intro hexch α z hz
    rw [← tubeTranslationInvariant_neg_rev_two E htrans α z hz]
    exact hexch α z hz
  · intro hidx α z hz
    rw [tubeTranslationInvariant_neg_rev_two E htrans α z hz]
    exact hidx α z hz

omit [Fintype ι] [DecidableEq ι] in
theorem twoPointSpinExchange_iff_twoPointIndexExchange_of_osTranslationInvariant
    {W : WightmanFamily ι} (E : TubeExtension W)
    (htrans : OSTranslationInvariant (schwingerFromTube E)) (ε : ℂ) :
    TwoPointSpinExchange ε E ↔ TwoPointIndexExchange ε E := by
  constructor
  · intro hexch α z hz
    rw [← tube_neg_rev_two_eq_of_osTranslationInvariant E htrans α z hz]
    exact hexch α z hz
  · intro hidx α z hz
    rw [tube_neg_rev_two_eq_of_osTranslationInvariant E htrans α z hz]
    exact hidx α z hz

omit [Fintype ι] [DecidableEq ι] in
theorem twoPointIndexExchange_iff_euclidTwoPointIndexExchange {W : WightmanFamily ι}
    (E : TubeExtension W) (ε : ℂ) :
    TwoPointIndexExchange ε E ↔ EuclidTwoPointIndexExchange ε (schwingerFromTube E) := by
  constructor
  · intro hidx α x hx
    exact hidx α (wickEmbedN 2 x)
      (wickEmbedN_mem_forward_tube_n 2 (posOrderedEuclidN_subset_orderedEuclidN 2 hx))
  · intro heuclid α z hz
    refine analyticOn_forward_tube_eq_of_posOrderedEuclidN_eq 2
      (E.analytic 2 α)
      (analyticOn_const.mul (E.analytic 2 (α ∘ Fin.rev)))
      (fun x hx => heuclid α x hx) hz

omit [Fintype ι] [DecidableEq ι] in
theorem twoPointSpinExchange_of_euclidTwoPointIndexExchange {W : WightmanFamily ι}
    (E : TubeExtension W) (htrans : OSTranslationInvariant (schwingerFromTube E))
    {ε : ℂ} (heuclid : EuclidTwoPointIndexExchange ε (schwingerFromTube E)) :
    TwoPointSpinExchange ε E :=
  (twoPointSpinExchange_iff_twoPointIndexExchange_of_osTranslationInvariant E htrans ε).mpr
    ((twoPointIndexExchange_iff_euclidTwoPointIndexExchange E ε).mpr heuclid)

namespace OSReconstructedWightman

variable {R : HolomorphicLorentzRep ι} {S : StarStructure R}
  {η : ℂ} {𝒮 : SchwingerFamily ι}

theorem schwingerFromTube_translation_invariant_of_os
    (P : OSReconstructedWightman R S η 𝒮) :
    OSTranslationInvariant (schwingerFromTube P.E) := by
  intro n α x hx a
  have hxa : (fun i => x i + a) ∈ orderedEuclidN n := by
    intro i hi
    change x i 0 + a 0 < x ⟨i.val + 1, hi⟩ 0 + a 0
    linarith [hx i hi]
  rw [← P.schwinger_eq n α (fun i => x i + a) hxa,
      ← P.schwinger_eq n α x hx]
  exact P.osAxioms.os1_translation n α x hx a

theorem tube_neg_rev_two_eq (P : OSReconstructedWightman R S η 𝒮)
    (α : Fin 2 → ι) (z : Fin 2 → Fin 4 → ℂ) (hz : z ∈ forward_tube_n 2) :
    P.E.H 2 α (-(z ∘ Fin.rev)) = P.E.H 2 α z :=
  tube_neg_rev_two_eq_of_osTranslationInvariant P.E
    P.schwingerFromTube_translation_invariant_of_os α z hz

theorem fermion_twoPoint_diag_wightman_eq_zero
    (P : OSReconstructedWightman R S (-1) 𝒮)
    (c : ι) (f : SchwartzMap (Fin 2 → Fin 4 → ℝ) ℂ) :
    P.W 2 (fun _ => c) f = 0 := by
  refine wightman_eq_zero_of_tube_eq_zero P.E 2 (fun _ => c) (fun z hz => ?_) f
  have h1 := P.tube_neg_rev_two_eq (fun _ => c) z hz
  have h2 := tubeWeakLocality_two P.tube_weakLocality (fun _ => c) z hz
  have h : P.E.H 2 (fun _ => c) z = (-1 : ℂ) * P.E.H 2 (fun _ => c) z := h1.symm.trans h2
  linear_combination (1 / 2 : ℂ) * h

theorem twoPointSpinExchange_of_euclid (P : OSReconstructedWightman R S η 𝒮)
    {ε : ℂ} (heuclid : EuclidTwoPointIndexExchange ε 𝒮) :
    TwoPointSpinExchange ε P.E := by
  refine twoPointSpinExchange_of_euclidTwoPointIndexExchange P.E
    P.schwingerFromTube_translation_invariant_of_os (fun α x hx => ?_)
  have hx' := posOrderedEuclidN_subset_orderedEuclidN 2 hx
  rw [← P.schwinger_eq 2 α x hx', ← P.schwinger_eq 2 (α ∘ Fin.rev) x hx']
  exact heuclid α x hx

theorem spin_statistics_of_euclidIndexExchange (P : OSReconstructedWightman R S η 𝒮)
    {ε : ℂ} (hε : R.HasSpinParity ε)
    (heuclid : EuclidTwoPointIndexExchange ε 𝒮)
    (h_nondeg : ∃ (α : Fin 2 → ι) (f : SchwartzMap (Fin 2 → Fin 4 → ℝ) ℂ), P.W 2 α f ≠ 0) :
    η = ε :=
  P.spin_statistics_of_twoPoint_ne_zero hε (P.twoPointSpinExchange_of_euclid heuclid) h_nondeg

end OSReconstructedWightman

theorem scalar_os_spin_statistics_unconditional {η : ℂ} {𝒮 : SchwingerFamily Unit}
    (P : ScalarOSReconstructedWightman η 𝒮)
    (h_nondeg : ∃ (α : Fin 2 → Unit) (f : SchwartzMap (Fin 2 → Fin 4 → ℝ) ℂ), P.W 2 α f ≠ 0) :
    η = 1 :=
  P.spin_statistics_of_twoPoint_ne_zero trivialRep_spinParity
    (twoPointSpinExchange_of_subsingleton_osTranslationInvariant P.E
      P.schwingerFromTube_translation_invariant_of_os)
    h_nondeg

theorem vector_os_spin_statistics_of_euclidIndexExchange {η : ℂ} {𝒮 : SchwingerFamily (Fin 4)}
    (P : VectorOSReconstructedWightman η 𝒮)
    (heuclid : EuclidTwoPointIndexExchange 1 𝒮)
    (h_nondeg : ∃ (α : Fin 2 → Fin 4) (f : SchwartzMap (Fin 2 → Fin 4 → ℝ) ℂ), P.W 2 α f ≠ 0) :
    η = 1 :=
  P.spin_statistics_of_euclidIndexExchange stdRep_spinParity heuclid h_nondeg

theorem dirac_os_spin_statistics_of_euclidIndexExchange
    {η : ℂ} {𝒮 : SchwingerFamily (Fin 2 ⊕ Fin 2)}
    (P : DiracOSReconstructedWightman η 𝒮)
    (heuclid : EuclidTwoPointIndexExchange (-1) 𝒮)
    (h_nondeg : ∃ (α : Fin 2 → Fin 2 ⊕ Fin 2)
      (f : SchwartzMap (Fin 2 → Fin 4 → ℝ) ℂ), P.W 2 α f ≠ 0) :
    η = -1 :=
  P.spin_statistics_of_euclidIndexExchange diracRep_spinParity heuclid h_nondeg

theorem spinorTensorBispinor_os_spin_statistics_of_euclidIndexExchange
    (m₁ m₂ : ℕ) {η : ℂ}
    {𝒮 : SchwingerFamily (((Fin m₁ → Fin 2) × (Fin m₂ → Fin 2)) ⊕
      ((Fin m₁ → Fin 2) × (Fin m₂ → Fin 2)))}
    (P : SpinorTensorBispinorOSReconstructedWightman m₁ m₂ η 𝒮)
    (heuclid : EuclidTwoPointIndexExchange ((-1 : ℂ) ^ (m₁ + m₂)) 𝒮)
    (h_nondeg : ∃ (α : Fin 2 → ((Fin m₁ → Fin 2) × (Fin m₂ → Fin 2)) ⊕
      ((Fin m₁ → Fin 2) × (Fin m₂ → Fin 2)))
      (f : SchwartzMap (Fin 2 → Fin 4 → ℝ) ℂ), P.W 2 α f ≠ 0) :
    η = (-1 : ℂ) ^ (m₁ + m₂) :=
  P.spin_statistics_of_euclidIndexExchange
    (directSumRep_spinParity (spinorTensorRep_spinParity m₁ m₂)
      (chiralSwapRep_spinParity (spinorTensorRep_spinParity m₁ m₂)))
    heuclid h_nondeg

@[simp]
lemma su2Conj_one : su2Conj 1 = 1 := by
  apply Subtype.ext
  simp [su2Conj]

lemma su2Conj_mul (U₁ U₂ : SU2) :
    su2Conj (U₁ * U₂) = su2Conj U₁ * su2Conj U₂ := by
  apply Subtype.ext
  change (((U₁ * U₂)⁻¹).val)ᵀ = (U₁⁻¹).valᵀ * (U₂⁻¹).valᵀ
  have h_inv : ((U₁ * U₂)⁻¹).val = (U₂⁻¹).val * (U₁⁻¹).val := by
    rw [_root_.mul_inv_rev]
    rfl
  rw [h_inv, Matrix.transpose_mul]

@[simp]
lemma su2Conj_inv (U : SU2) :
    su2Conj U⁻¹ = (su2Conj U)⁻¹ := by
  apply mul_left_cancel (a := su2Conj U)
  rw [← su2Conj_mul, mul_inv_cancel, mul_inv_cancel, su2Conj_one]

@[simp]
lemma su2Conj_involutive (U : SU2) :
    su2Conj (su2Conj U) = U := by
  apply Subtype.ext
  change (((su2Conj U)⁻¹).val)ᵀ = U.val
  rw [← su2Conj_inv, su2Conj_val_transpose, inv_inv]

@[simp]
lemma negOneSU2_inv : negOneSU2⁻¹ = negOneSU2 := by
  apply mul_left_cancel (a := negOneSU2)
  rw [mul_inv_cancel]
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [negOneSU2]

@[simp]
lemma su2Conj_negOneSU2 : su2Conj negOneSU2 = negOneSU2 := by
  apply Subtype.ext
  change ((negOneSU2⁻¹).val)ᵀ = negOneSU2.val
  rw [negOneSU2_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [negOneSU2]

lemma su2Conj_val_eq_map_star (U : SU2) :
    (su2Conj U).val = U.val.map star := by
  have h_inv : (U⁻¹).val = U.valᴴ := rfl
  change (U⁻¹).valᵀ = U.val.map star
  rw [h_inv]
  ext i j
  simp [Matrix.transpose_apply, Matrix.conjTranspose_apply]

@[simp]
lemma su2ToSL2C_su2Conj (U : SU2) :
    su2ToSL2C (su2Conj U) = sl2c_conj (su2ToSL2C U) := by
  apply Subtype.ext
  change (su2Conj U).val = (su2ToSL2C U).val.map star
  exact su2Conj_val_eq_map_star U

@[simp]
lemma sl2c_conj_su2ToSL2C_su2Conj (U : SU2) :
    sl2c_conj (su2ToSL2C (su2Conj U)) = su2ToSL2C U := by
  rw [← su2ToSL2C_su2Conj, su2Conj_involutive]

@[simp]
lemma euclidRotN_one (n : ℕ) (x : Fin n → Fin 4 → ℝ) :
    euclidRotN n 1 1 x = x := by
  ext i μ
  dsimp [euclidRotN]
  rw [euclidRotOfSU2_one, Matrix.one_mulVec]

lemma euclidRotN_mul (n : ℕ) (U₁ U₂ V₁ V₂ : SU2) (x : Fin n → Fin 4 → ℝ) :
    euclidRotN n (U₁ * U₂) (V₁ * V₂) x =
      euclidRotN n U₁ V₁ (euclidRotN n U₂ V₂ x) := by
  ext i μ
  dsimp [euclidRotN]
  rw [euclidRotOfSU2_mul, Matrix.mulVec_mulVec]

@[simp]
lemma euclidRotN_negOne_negOne (n : ℕ) (x : Fin n → Fin 4 → ℝ) :
    euclidRotN n negOneSU2 negOneSU2 x = x := by
  ext i μ
  dsimp [euclidRotN]
  rw [euclidRotOfSU2_mulVec, euclidRotApply_negOne_negOne]

omit [Fintype ι] [DecidableEq ι] in
lemma osConfig_mk_eq_of_val_eq {n : ℕ} {α : Fin n → ι}
    {x₁ x₂ : posOrderedEuclidN n} (h : x₁.val = x₂.val) :
    (⟨n, (α, x₁)⟩ : OSConfig ι) = ⟨n, (α, x₂)⟩ := by
  cases Subtype.ext h
  rfl

omit [Fintype ι] [DecidableEq ι] in
lemma osConfigPointRot_mk (U : SU2) (n : ℕ) (α : Fin n → ι) (x : posOrderedEuclidN n) :
    osConfigPointRot U ⟨n, (α, x)⟩ =
      ⟨n, (α, ⟨euclidRotN n U (su2Conj U) x.val,
        euclidRotN_su2Conj_mem_posOrderedEuclidN n U x.property⟩)⟩ := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma osConfigPointRot_one (A : OSConfig ι) :
    osConfigPointRot 1 A = A := by
  rcases A with ⟨n, α, x⟩
  rw [osConfigPointRot_mk]
  apply osConfig_mk_eq_of_val_eq
  change euclidRotN n 1 (su2Conj 1) x.val = x.val
  rw [su2Conj_one, euclidRotN_one]

omit [Fintype ι] [DecidableEq ι] in
lemma osConfigPointRot_mul (U₁ U₂ : SU2) (A : OSConfig ι) :
    osConfigPointRot (U₁ * U₂) A = osConfigPointRot U₁ (osConfigPointRot U₂ A) := by
  rcases A with ⟨n, α, x⟩
  rw [osConfigPointRot_mk, osConfigPointRot_mk, osConfigPointRot_mk]
  apply osConfig_mk_eq_of_val_eq
  change euclidRotN n (U₁ * U₂) (su2Conj (U₁ * U₂)) x.val =
    euclidRotN n U₁ (su2Conj U₁) (euclidRotN n U₂ (su2Conj U₂) x.val)
  rw [su2Conj_mul, euclidRotN_mul]

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma osConfigPointRot_negOneSU2 (A : OSConfig ι) :
    osConfigPointRot negOneSU2 A = A := by
  rcases A with ⟨n, α, x⟩
  rw [osConfigPointRot_mk]
  apply osConfig_mk_eq_of_val_eq
  change euclidRotN n negOneSU2 (su2Conj negOneSU2) x.val = x.val
  rw [su2Conj_negOneSU2, euclidRotN_negOne_negOne]

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma osConfigPointRot_vacuum (U : SU2) :
    osConfigPointRot U (osVacuumConfig ι) = osVacuumConfig ι := by
  dsimp [osVacuumConfig]
  rw [osConfigPointRot_mk]
  apply osConfig_mk_eq_of_val_eq
  ext i μ
  exact Fin.elim0 i

@[simp]
lemma osSpatialRotLM_one {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) :
    osSpatialRotLM D 1 = LinearMap.id := by
  unfold osSpatialRotLM
  have h_id : osConfigPointRot (ι := ι) 1 = id := funext osConfigPointRot_one
  rw [h_id, osLiftConfigMap_id]

lemma osSpatialRotLM_mul {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (U₁ U₂ : SU2) :
    osSpatialRotLM D (U₁ * U₂) = (osSpatialRotLM D U₁).comp (osSpatialRotLM D U₂) := by
  unfold osSpatialRotLM
  have h_mul : osConfigPointRot (ι := ι) (U₁ * U₂) =
      osConfigPointRot U₁ ∘ osConfigPointRot U₂ := funext (osConfigPointRot_mul U₁ U₂)
  rw [h_mul, osLiftConfigMap_comp]

@[simp]
lemma osSpatialRotLM_negOneSU2 {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) :
    osSpatialRotLM D negOneSU2 = LinearMap.id := by
  unfold osSpatialRotLM
  have h_id : osConfigPointRot (ι := ι) negOneSU2 = id := funext osConfigPointRot_negOneSU2
  rw [h_id, osLiftConfigMap_id]

@[simp]
lemma osSpatialRotLM_osVacuumPre {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (U : SU2) :
    osSpatialRotLM D U (osVacuumPre D) = osVacuumPre D := by
  unfold osSpatialRotLM osVacuumPre
  rw [osLiftConfigMap_osBasisPre, osConfigPointRot_vacuum]

def osSpinorRotMatrix (R : HolomorphicLorentzRep ι) (U : SU2) : Matrix ι ι ℂ :=
  R.σ (su2ToSL2C U, su2ToSL2C (su2Conj U))

@[simp]
lemma osSpinorRotMatrix_one (R : HolomorphicLorentzRep ι) :
    osSpinorRotMatrix R 1 = 1 := by
  dsimp [osSpinorRotMatrix]
  rw [su2Conj_one, su2ToSL2C_one]
  exact R.σ.map_one

lemma osSpinorRotMatrix_mul (R : HolomorphicLorentzRep ι) (U₁ U₂ : SU2) :
    osSpinorRotMatrix R (U₁ * U₂) = osSpinorRotMatrix R U₁ * osSpinorRotMatrix R U₂ := by
  dsimp [osSpinorRotMatrix]
  rw [su2Conj_mul, su2ToSL2C_mul, su2ToSL2C_mul]
  exact R.σ.map_mul (su2ToSL2C U₁, su2ToSL2C (su2Conj U₁))
    (su2ToSL2C U₂, su2ToSL2C (su2Conj U₂))

@[simp]
lemma osSpinorRotMatrix_inv_mul_self (R : HolomorphicLorentzRep ι) (U : SU2) :
    osSpinorRotMatrix R U⁻¹ * osSpinorRotMatrix R U = 1 := by
  rw [← osSpinorRotMatrix_mul, inv_mul_cancel, osSpinorRotMatrix_one]

@[simp]
lemma osSpinorRotMatrix_mul_inv_self (R : HolomorphicLorentzRep ι) (U : SU2) :
    osSpinorRotMatrix R U * osSpinorRotMatrix R U⁻¹ = 1 := by
  rw [← osSpinorRotMatrix_mul, mul_inv_cancel, osSpinorRotMatrix_one]

lemma osSpinorRotMatrix_negOneSU2 (R : HolomorphicLorentzRep ι) {ε : ℂ}
    (hε : R.HasSpinParity ε) :
    osSpinorRotMatrix R negOneSU2 = ε • 1 := by
  dsimp [osSpinorRotMatrix]
  rw [su2Conj_negOneSU2, su2ToSL2C_negOneSU2]
  exact hε.1

@[simp]
lemma osSpinorRotMatrix_trivialRep (U : SU2) :
    osSpinorRotMatrix trivialRep U = 1 := rfl

theorem starStructure_intertwine_osSpinorRotMatrix {R : HolomorphicLorentzRep ι}
    (S : StarStructure R) (U : SU2) :
    S.C * osSpinorRotMatrix R U = (osSpinorRotMatrix R U).map star * S.C := by
  dsimp [osSpinorRotMatrix]
  have h := S.intertwine (su2ToSL2C U) (su2ToSL2C (su2Conj U))
  rwa [sl2c_conj_su2ToSL2C_su2Conj, ← su2ToSL2C_su2Conj] at h

theorem star_osSpinorRotMatrix_inv_mul_C_mul {R : HolomorphicLorentzRep ι}
    (S : StarStructure R) (U : SU2) :
    (osSpinorRotMatrix R U⁻¹).map star * S.C * osSpinorRotMatrix R U = S.C := by
  rw [Matrix.mul_assoc, starStructure_intertwine_osSpinorRotMatrix S U,
      ← Matrix.mul_assoc]
  have h_inv : (osSpinorRotMatrix R U⁻¹).map star * (osSpinorRotMatrix R U).map star = 1 := by
    ext a b
    have h1 := congrFun (congrFun (osSpinorRotMatrix_inv_mul_self R U) a) b
    have h2 := congrArg (starRingEnd ℂ) h1
    simp only [Matrix.mul_apply, Matrix.map_apply, map_sum, map_mul, starRingEnd_apply] at h2 ⊢
    rw [h2]
    by_cases hab : a = b <;> simp [hab, Matrix.one_apply]
  rw [h_inv, Matrix.one_mul]

lemma osPreHilbert_eq_finsupp_sum_osBasisPre {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (Ψ : OSPreHilbertSpace D) :
    Ψ = Ψ.toFinsupp.sum (fun A c => c • osBasisPre D A) := by
  apply OSPreHilbertSpace.ext
  have h_map : (Ψ.toFinsupp.sum (fun A c => c • osBasisPre D A)).toFinsupp =
      Ψ.toFinsupp.sum (fun A c => c • (osBasisPre D A).toFinsupp) :=
    map_finsuppSum (OSPreHilbertSpace.equivFinsupp D).toLinearMap Ψ.toFinsupp
      (fun A c => c • osBasisPre D A)
  rw [h_map]
  have h_single : (fun (A : OSConfig ι) (c : ℂ) => c • (osBasisPre D A).toFinsupp) =
      fun A c => Finsupp.single A c := by
    ext A c B
    simp [osBasisPre]
  rw [h_single, Finsupp.sum_single]

lemma osPreHilbert_linearMap_ext {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {D : OSReflectionPositiveData R S} {E : Type*} [AddCommMonoid E] [Module ℂ E]
    {L₁ L₂ : OSPreHilbertSpace D →ₗ[ℂ] E}
    (h : ∀ A : OSConfig ι, L₁ (osBasisPre D A) = L₂ (osBasisPre D A)) :
    L₁ = L₂ := by
  ext Ψ
  rw [osPreHilbert_eq_finsupp_sum_osBasisPre D Ψ, map_finsuppSum, map_finsuppSum]
  refine Finsupp.sum_congr (fun A _ => ?_)
  rw [L₁.map_smul, L₂.map_smul, h A]

lemma osPreHilbert_inner_map_eq_of_osBasisPre₂ {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S)
    (L₁ L₂ : OSPreHilbertSpace D →ₗ[ℂ] OSPreHilbertSpace D)
    (h : ∀ A B : OSConfig ι,
      ⟪L₁ (osBasisPre D A), L₁ (osBasisPre D B)⟫_ℂ =
        ⟪L₂ (osBasisPre D A), L₂ (osBasisPre D B)⟫_ℂ)
    (Ψ Φ : OSPreHilbertSpace D) :
    ⟪L₁ Ψ, L₁ Φ⟫_ℂ = ⟪L₂ Ψ, L₂ Φ⟫_ℂ := by
  have hL : ∀ (L : OSPreHilbertSpace D →ₗ[ℂ] OSPreHilbertSpace D) (X : OSPreHilbertSpace D),
      L X = ∑ A ∈ X.toFinsupp.support, X.toFinsupp A • L (osBasisPre D A) := by
    intro L X
    conv_lhs => rw [osPreHilbert_eq_finsupp_sum_osBasisPre D X]
    rw [map_finsuppSum]
    unfold Finsupp.sum
    refine Finset.sum_congr rfl (fun A _ => L.map_smul _ _)
  rw [hL L₁ Ψ, hL L₁ Φ, hL L₂ Ψ, hL L₂ Φ, sum_inner, sum_inner]
  refine Finset.sum_congr rfl (fun A _ => ?_)
  rw [inner_smul_left, inner_smul_left, inner_sum, inner_sum]
  congr 1
  refine Finset.sum_congr rfl (fun B _ => ?_)
  rw [inner_smul_right, inner_smul_right, h A B]

def osConfigSetIdx (A : OSConfig ι) (δ : Fin A.1 → ι) : OSConfig ι :=
  ⟨A.1, (δ, A.2.2)⟩

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma osConfigSetIdx_fst (A : OSConfig ι) (δ : Fin A.1 → ι) :
    (osConfigSetIdx A δ).1 = A.1 := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma osConfigSetIdx_snd_fst (A : OSConfig ι) (δ : Fin A.1 → ι) :
    (osConfigSetIdx A δ).2.1 = δ := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma osConfigSetIdx_snd_snd (A : OSConfig ι) (δ : Fin A.1 → ι) :
    (osConfigSetIdx A δ).2.2 = A.2.2 := rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma osConfigSetIdx_self (A : OSConfig ι) :
    osConfigSetIdx A A.2.1 = A := by
  rcases A with ⟨n, α, x⟩
  rfl

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma osConfigSetIdx_osConfigSetIdx (A : OSConfig ι) (δ γ : Fin A.1 → ι) :
    osConfigSetIdx (osConfigSetIdx A δ) γ = osConfigSetIdx A γ := rfl

def osSpinorIdxSingle {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (M : Matrix ι ι ℂ) (A : OSConfig ι) :
    OSPreHilbertSpace D :=
  ∑ δ : Fin A.1 → ι,
    (∏ i : Fin A.1, M (A.2.1 i) (δ i)) • osBasisPre D (osConfigSetIdx A δ)

def osSpinorIdxLM {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (M : Matrix ι ι ℂ) :
    OSPreHilbertSpace D →ₗ[ℂ] OSPreHilbertSpace D :=
  (Finsupp.lsum ℂ (fun A =>
    LinearMap.toSpanSingleton ℂ (OSPreHilbertSpace D) (osSpinorIdxSingle D M A))).comp
    (OSPreHilbertSpace.equivFinsupp D).toLinearMap

@[simp]
lemma osSpinorIdxLM_osBasisPre {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (M : Matrix ι ι ℂ) (A : OSConfig ι) :
    osSpinorIdxLM D M (osBasisPre D A) = osSpinorIdxSingle D M A := by
  dsimp [osSpinorIdxLM, osBasisPre, OSPreHilbertSpace.equivFinsupp]
  simp

lemma osSpinorIdxSingle_smul_one {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (c : ℂ) (A : OSConfig ι) :
    osSpinorIdxSingle D (c • (1 : Matrix ι ι ℂ)) A = (c ^ A.1) • osBasisPre D A := by
  unfold osSpinorIdxSingle
  have h_prod : ∀ δ : Fin A.1 → ι,
      (∏ i : Fin A.1, (c • (1 : Matrix ι ι ℂ)) (A.2.1 i) (δ i)) =
        if A.2.1 = δ then c ^ A.1 else 0 := by
    intro δ
    by_cases h : A.2.1 = δ
    · subst h
      simp
    · rw [if_neg h]
      obtain ⟨i, hi⟩ : ∃ i, A.2.1 i ≠ δ i := by
        by_contra hc
        push Not at hc
        exact h (funext hc)
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [Matrix.one_apply_ne hi])
  simp_rw [h_prod, ite_smul, zero_smul]
  simp

@[simp]
lemma osSpinorIdxLM_one {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) :
    osSpinorIdxLM D 1 = LinearMap.id := by
  apply osPreHilbert_linearMap_ext
  intro A
  have h := osSpinorIdxSingle_smul_one D 1 A
  rw [one_smul, one_pow, one_smul] at h
  rw [osSpinorIdxLM_osBasisPre, h, LinearMap.id_apply]

@[simp]
lemma osSpinorIdxLM_osVacuumPre {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (M : Matrix ι ι ℂ) :
    osSpinorIdxLM D M (osVacuumPre D) = osVacuumPre D := by
  unfold osVacuumPre
  rw [osSpinorIdxLM_osBasisPre]
  unfold osSpinorIdxSingle osVacuumConfig
  dsimp only
  rw [Finset.univ_unique, Finset.sum_singleton]
  have h_prod : (∏ i : Fin 0, M (Fin.elim0 i) ((default : Fin 0 → ι) i)) = 1 :=
    Finset.prod_eq_one (fun i _ => Fin.elim0 i)
  have h_idx : (default : Fin 0 → ι) = Fin.elim0 := Subsingleton.elim _ _
  rw [h_prod, one_smul, h_idx]
  rfl

lemma osSpinorIdxLM_comp {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (M₁ M₂ : Matrix ι ι ℂ) :
    (osSpinorIdxLM D M₁).comp (osSpinorIdxLM D M₂) = osSpinorIdxLM D (M₂ * M₁) := by
  apply osPreHilbert_linearMap_ext
  intro A
  rw [LinearMap.comp_apply, osSpinorIdxLM_osBasisPre, osSpinorIdxLM_osBasisPre]
  unfold osSpinorIdxSingle
  rw [map_sum]
  simp_rw [map_smul, osSpinorIdxLM_osBasisPre]
  unfold osSpinorIdxSingle
  simp_rw [osConfigSetIdx_fst, osConfigSetIdx_snd_fst, osConfigSetIdx_osConfigSetIdx,
    Finset.smul_sum, smul_smul]
  have h_comm :
      (∑ δ : Fin A.1 → ι, ∑ γ : Fin A.1 → ι,
        ((∏ i : Fin A.1, M₂ (A.2.1 i) (δ i)) * ∏ i : Fin A.1, M₁ (δ i) (γ i)) •
          osBasisPre D (osConfigSetIdx A γ)) =
      ∑ γ : Fin A.1 → ι, ∑ δ : Fin A.1 → ι,
        ((∏ i : Fin A.1, M₂ (A.2.1 i) (δ i)) * ∏ i : Fin A.1, M₁ (δ i) (γ i)) •
          osBasisPre D (osConfigSetIdx A γ) := Finset.sum_comm
  refine h_comm.trans ?_
  refine Finset.sum_congr rfl (fun γ _ => ?_)
  rw [← Finset.sum_smul]
  congr 1
  simp_rw [← Finset.prod_mul_distrib]
  have h_ps := (Fintype.prod_sum
    (fun (i : Fin A.1) (d : ι) => M₂ (A.2.1 i) d * M₁ d (γ i))).symm
  rw [h_ps]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  simp [Matrix.mul_apply]

lemma osSpatialRotLM_comp_osSpinorIdxLM {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (U : SU2) (M : Matrix ι ι ℂ) :
    (osSpatialRotLM D U).comp (osSpinorIdxLM D M) =
      (osSpinorIdxLM D M).comp (osSpatialRotLM D U) := by
  apply osPreHilbert_linearMap_ext
  intro A
  rw [LinearMap.comp_apply, LinearMap.comp_apply, osSpinorIdxLM_osBasisPre]
  unfold osSpatialRotLM
  rw [osLiftConfigMap_osBasisPre, osSpinorIdxLM_osBasisPre]
  unfold osSpinorIdxSingle
  rw [map_sum]
  refine Finset.sum_congr rfl (fun δ _ => ?_)
  rw [map_smul, osLiftConfigMap_osBasisPre]
  rfl

lemma osTimeShiftLM_comp_osSpinorIdxLM {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (τ : ℝ) (hτ : 0 ≤ τ) (M : Matrix ι ι ℂ) :
    (osTimeShiftLM D τ hτ).comp (osSpinorIdxLM D M) =
      (osSpinorIdxLM D M).comp (osTimeShiftLM D τ hτ) := by
  apply osPreHilbert_linearMap_ext
  intro A
  rw [LinearMap.comp_apply, LinearMap.comp_apply, osSpinorIdxLM_osBasisPre]
  unfold osTimeShiftLM
  rw [osLiftConfigMap_osBasisPre, osSpinorIdxLM_osBasisPre]
  unfold osSpinorIdxSingle
  rw [map_sum]
  refine Finset.sum_congr rfl (fun δ _ => ?_)
  rw [map_smul, osLiftConfigMap_osBasisPre]
  rfl

def OSSpinorRotCovariant (R : HolomorphicLorentzRep ι) (𝒮 : SchwingerFamily ι) : Prop :=
  ∀ (n : ℕ) (U : SU2) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
    x ∈ orderedEuclidN n →
    𝒮 n α (euclidRotN n U (su2Conj U) x) =
      ∑ β : Fin n → ι,
        (∏ i : Fin n, osSpinorRotMatrix R U (α i) (β i)) * 𝒮 n β x

lemma euclidRotN_su2Conj_mem_orderedEuclidN (n : ℕ) (U : SU2)
    {x : Fin n → Fin 4 → ℝ} (hx : x ∈ orderedEuclidN n) :
    euclidRotN n U (su2Conj U) x ∈ orderedEuclidN n := by
  intro i hi
  dsimp [euclidRotN]
  rw [euclidRotOfSU2_mulVec, euclidRotOfSU2_mulVec,
      euclidRotApply_su2Conj_time, euclidRotApply_su2Conj_time]
  exact hx i hi

lemma OSAxioms.osSpinorRotCovariant {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {η : ℂ} {𝒮 : SchwingerFamily ι} (hOS : OSAxioms R S η 𝒮) :
    OSSpinorRotCovariant R 𝒮 := by
  intro n U α x hx
  exact hOS.os1_rotation n U (su2Conj U) x hx
    (euclidRotN_su2Conj_mem_orderedEuclidN n U hx) α

theorem inner_osSpatialRotLM_eq_osSpinorIdxLM {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (hrot : OSSpinorRotCovariant R D.𝒮)
    (U : SU2) (Ψ Φ : OSPreHilbertSpace D) :
    ⟪osSpatialRotLM D U Ψ, osSpatialRotLM D U Φ⟫_ℂ =
      ⟪osSpinorIdxLM D (osSpinorRotMatrix R U) Ψ,
        osSpinorIdxLM D (osSpinorRotMatrix R U) Φ⟫_ℂ := by
  refine osPreHilbert_inner_map_eq_of_osBasisPre₂ D
    (osSpatialRotLM D U) (osSpinorIdxLM D (osSpinorRotMatrix R U)) (fun A B => ?_) Ψ Φ
  unfold osSpatialRotLM
  rw [osLiftConfigMap_osBasisPre, osLiftConfigMap_osBasisPre, inner_osBasisPre,
      osSpinorIdxLM_osBasisPre, osSpinorIdxLM_osBasisPre]
  unfold osSpinorIdxSingle
  rw [sum_inner]
  simp_rw [inner_smul_left, inner_sum, inner_smul_right, inner_osBasisPre]
  rcases A with ⟨j, α, x, hx⟩
  rcases B with ⟨k, α', y, hy⟩
  unfold osKernel osConfigPointRot osConfigSetIdx
  dsimp only
  have h_ord : osConcatPoint j k x y ∈ orderedEuclidN (j + k) :=
    osConcatPoint_mem_orderedEuclidN j k hx hy
  have h_lhs_term : ∀ β : Fin j → ι,
      (∏ i : Fin j, S.C (α i) (β i)) *
        D.𝒮 (j + k) (osConcatIdx j k β α')
          (osConcatPoint j k (euclidRotN j U (su2Conj U) x) (euclidRotN k U (su2Conj U) y)) =
      ∑ δL : Fin j → ι, ∑ δR : Fin k → ι,
        (∏ i : Fin j, S.C (α i) (β i) * osSpinorRotMatrix R U (β i) (δL i)) *
          ((∏ r : Fin k, osSpinorRotMatrix R U (α' r) (δR r)) *
            D.𝒮 (j + k) (osConcatIdx j k δL δR) (osConcatPoint j k x y)) := by
    intro β
    rw [osConcatPoint_euclidRotN_su2Conj,
        hrot (j + k) U (osConcatIdx j k β α') (osConcatPoint j k x y) h_ord,
        ← (osConcatIdxEquiv j k).sum_comp, Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun δL _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun δR _ => ?_)
    dsimp [osConcatIdxEquiv]
    rw [prod_osConcatIdx j k (fun a b => osSpinorRotMatrix R U a b) β δL α' δR]
    have h_mul : (∏ i : Fin j, S.C (α i) (β i)) *
        (∏ i : Fin j, osSpinorRotMatrix R U (β i) (δL i)) =
        ∏ i : Fin j, S.C (α i) (β i) * osSpinorRotMatrix R U (β i) (δL i) :=
      (Finset.prod_mul_distrib).symm
    calc (∏ i : Fin j, S.C (α i) (β i)) *
          (((∏ i : Fin j, osSpinorRotMatrix R U (β i) (δL i)) *
            ∏ r : Fin k, osSpinorRotMatrix R U (α' r) (δR r)) *
            D.𝒮 (j + k) (osConcatIdx j k δL δR) (osConcatPoint j k x y))
      _ = ((∏ i : Fin j, S.C (α i) (β i)) *
            ∏ i : Fin j, osSpinorRotMatrix R U (β i) (δL i)) *
            ((∏ r : Fin k, osSpinorRotMatrix R U (α' r) (δR r)) *
              D.𝒮 (j + k) (osConcatIdx j k δL δR) (osConcatPoint j k x y)) := by ring
      _ = (∏ i : Fin j, S.C (α i) (β i) * osSpinorRotMatrix R U (β i) (δL i)) *
            ((∏ r : Fin k, osSpinorRotMatrix R U (α' r) (δR r)) *
              D.𝒮 (j + k) (osConcatIdx j k δL δR) (osConcatPoint j k x y)) := by rw [h_mul]
  simp_rw [h_lhs_term]
  rw [Finset.sum_comm]
  have h_lhs_collapse : ∀ δL : Fin j → ι,
      (∑ β : Fin j → ι, ∑ δR : Fin k → ι,
        (∏ i : Fin j, S.C (α i) (β i) * osSpinorRotMatrix R U (β i) (δL i)) *
          ((∏ r : Fin k, osSpinorRotMatrix R U (α' r) (δR r)) *
            D.𝒮 (j + k) (osConcatIdx j k δL δR) (osConcatPoint j k x y))) =
      ∑ δR : Fin k → ι,
        (∏ i : Fin j, (S.C * osSpinorRotMatrix R U) (α i) (δL i)) *
          ((∏ r : Fin k, osSpinorRotMatrix R U (α' r) (δR r)) *
            D.𝒮 (j + k) (osConcatIdx j k δL δR) (osConcatPoint j k x y)) := by
    intro δL
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun δR _ => ?_)
    rw [← Finset.sum_mul]
    congr 1
    have h_ps := (Fintype.prod_sum
      (fun (i : Fin j) (b : ι) => S.C (α i) b * osSpinorRotMatrix R U b (δL i))).symm
    rw [h_ps]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    simp [Matrix.mul_apply]
  simp_rw [h_lhs_collapse, starStructure_intertwine_osSpinorRotMatrix S U]
  have h_rhs :
      (∑ δ : Fin j → ι, (starRingEnd ℂ) (∏ i : Fin j, osSpinorRotMatrix R U (α i) (δ i)) *
        ∑ δR : Fin k → ι, (∏ r : Fin k, osSpinorRotMatrix R U (α' r) (δR r)) *
          ∑ δL : Fin j → ι, (∏ i : Fin j, S.C (δ i) (δL i)) *
            D.𝒮 (j + k) (osConcatIdx j k δL δR) (osConcatPoint j k x y)) =
      ∑ δR : Fin k → ι, ∑ δL : Fin j → ι,
        (∏ i : Fin j, ((osSpinorRotMatrix R U).map star * S.C) (α i) (δL i)) *
          ((∏ r : Fin k, osSpinorRotMatrix R U (α' r) (δR r)) *
            D.𝒮 (j + k) (osConcatIdx j k δL δR) (osConcatPoint j k x y)) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun δR _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun δL _ => ?_)
    have h_inner : ∀ δ : Fin j → ι,
        (starRingEnd ℂ) (∏ i : Fin j, osSpinorRotMatrix R U (α i) (δ i)) *
          ((∏ r : Fin k, osSpinorRotMatrix R U (α' r) (δR r)) *
            ((∏ i : Fin j, S.C (δ i) (δL i)) *
              D.𝒮 (j + k) (osConcatIdx j k δL δR) (osConcatPoint j k x y))) =
        (∏ i : Fin j, star (osSpinorRotMatrix R U (α i) (δ i)) * S.C (δ i) (δL i)) *
          ((∏ r : Fin k, osSpinorRotMatrix R U (α' r) (δR r)) *
            D.𝒮 (j + k) (osConcatIdx j k δL δR) (osConcatPoint j k x y)) := by
      intro δ
      rw [map_prod]
      have h_pm : (∏ i : Fin j, (starRingEnd ℂ) (osSpinorRotMatrix R U (α i) (δ i))) *
          (∏ i : Fin j, S.C (δ i) (δL i)) =
          ∏ i : Fin j, star (osSpinorRotMatrix R U (α i) (δ i)) * S.C (δ i) (δL i) :=
        (Finset.prod_mul_distrib).symm
      calc (∏ i : Fin j, (starRingEnd ℂ) (osSpinorRotMatrix R U (α i) (δ i))) *
            ((∏ r : Fin k, osSpinorRotMatrix R U (α' r) (δR r)) *
              ((∏ i : Fin j, S.C (δ i) (δL i)) *
                D.𝒮 (j + k) (osConcatIdx j k δL δR) (osConcatPoint j k x y)))
        _ = ((∏ i : Fin j, (starRingEnd ℂ) (osSpinorRotMatrix R U (α i) (δ i))) *
              ∏ i : Fin j, S.C (δ i) (δL i)) *
              ((∏ r : Fin k, osSpinorRotMatrix R U (α' r) (δR r)) *
                D.𝒮 (j + k) (osConcatIdx j k δL δR) (osConcatPoint j k x y)) := by ring
        _ = (∏ i : Fin j, star (osSpinorRotMatrix R U (α i) (δ i)) * S.C (δ i) (δL i)) *
              ((∏ r : Fin k, osSpinorRotMatrix R U (α' r) (δR r)) *
                D.𝒮 (j + k) (osConcatIdx j k δL δR) (osConcatPoint j k x y)) := by rw [h_pm]
    simp_rw [h_inner, ← Finset.sum_mul]
    congr 1
    have h_ps := (Fintype.prod_sum
      (fun (i : Fin j) (d : ι) => star (osSpinorRotMatrix R U (α i) d) * S.C d (δL i))).symm
    rw [h_ps]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    simp [Matrix.mul_apply]
  rw [h_rhs, Finset.sum_comm]

def osSpinorRotLM {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (U : SU2) :
    OSPreHilbertSpace D →ₗ[ℂ] OSPreHilbertSpace D :=
  (osSpatialRotLM D U).comp (osSpinorIdxLM D (osSpinorRotMatrix R U⁻¹))

@[simp]
lemma osSpinorRotLM_one {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) :
    osSpinorRotLM D 1 = LinearMap.id := by
  unfold osSpinorRotLM
  rw [inv_one, osSpinorRotMatrix_one, osSpinorIdxLM_one, osSpatialRotLM_one, LinearMap.id_comp]

lemma osSpinorRotLM_mul {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (U₁ U₂ : SU2) :
    osSpinorRotLM D (U₁ * U₂) = (osSpinorRotLM D U₁).comp (osSpinorRotLM D U₂) := by
  unfold osSpinorRotLM
  rw [_root_.mul_inv_rev, osSpinorRotMatrix_mul, ← osSpinorIdxLM_comp, osSpatialRotLM_mul]
  calc ((osSpatialRotLM D U₁).comp (osSpatialRotLM D U₂)).comp
        ((osSpinorIdxLM D (osSpinorRotMatrix R U₁⁻¹)).comp
          (osSpinorIdxLM D (osSpinorRotMatrix R U₂⁻¹)))
    _ = (osSpatialRotLM D U₁).comp
          (((osSpatialRotLM D U₂).comp (osSpinorIdxLM D (osSpinorRotMatrix R U₁⁻¹))).comp
            (osSpinorIdxLM D (osSpinorRotMatrix R U₂⁻¹))) := by
        ext Ψ; rfl
    _ = (osSpatialRotLM D U₁).comp
          (((osSpinorIdxLM D (osSpinorRotMatrix R U₁⁻¹)).comp (osSpatialRotLM D U₂)).comp
            (osSpinorIdxLM D (osSpinorRotMatrix R U₂⁻¹))) := by
        rw [osSpatialRotLM_comp_osSpinorIdxLM]
    _ = ((osSpatialRotLM D U₁).comp (osSpinorIdxLM D (osSpinorRotMatrix R U₁⁻¹))).comp
          ((osSpatialRotLM D U₂).comp (osSpinorIdxLM D (osSpinorRotMatrix R U₂⁻¹))) := by
        ext Ψ; rfl

@[simp]
lemma osSpinorRotLM_osVacuumPre {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (U : SU2) :
    osSpinorRotLM D U (osVacuumPre D) = osVacuumPre D := by
  unfold osSpinorRotLM
  rw [LinearMap.comp_apply, osSpinorIdxLM_osVacuumPre, osSpatialRotLM_osVacuumPre]

theorem osSpinorRotLM_negOneSU2_osBasisPre {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) {ε : ℂ} (hε : R.HasSpinParity ε) (A : OSConfig ι) :
    osSpinorRotLM D negOneSU2 (osBasisPre D A) = (ε ^ A.1) • osBasisPre D A := by
  unfold osSpinorRotLM
  rw [LinearMap.comp_apply, negOneSU2_inv, osSpinorRotMatrix_negOneSU2 R hε,
      osSpinorIdxLM_osBasisPre, osSpinorIdxSingle_smul_one, osSpatialRotLM_negOneSU2,
      LinearMap.id_apply]

lemma osSpinorRotLM_comm_osTimeShiftLM {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (U : SU2) (τ : ℝ) (hτ : 0 ≤ τ) :
    (osSpinorRotLM D U).comp (osTimeShiftLM D τ hτ) =
      (osTimeShiftLM D τ hτ).comp (osSpinorRotLM D U) := by
  unfold osSpinorRotLM
  have h_pt : (osSpatialRotLM D U).comp (osTimeShiftLM D τ hτ) =
      (osTimeShiftLM D τ hτ).comp (osSpatialRotLM D U) := by
    unfold osSpatialRotLM osTimeShiftLM
    rw [← osLiftConfigMap_comp, ← osLiftConfigMap_comp,
        osConfigPointRot_comm_osConfigTimeShift]
  calc ((osSpatialRotLM D U).comp (osSpinorIdxLM D (osSpinorRotMatrix R U⁻¹))).comp
        (osTimeShiftLM D τ hτ)
    _ = (osSpatialRotLM D U).comp
          ((osSpinorIdxLM D (osSpinorRotMatrix R U⁻¹)).comp (osTimeShiftLM D τ hτ)) := by
        ext Ψ; rfl
    _ = (osSpatialRotLM D U).comp
          ((osTimeShiftLM D τ hτ).comp (osSpinorIdxLM D (osSpinorRotMatrix R U⁻¹))) := by
        rw [← osTimeShiftLM_comp_osSpinorIdxLM]
    _ = ((osSpatialRotLM D U).comp (osTimeShiftLM D τ hτ)).comp
          (osSpinorIdxLM D (osSpinorRotMatrix R U⁻¹)) := by
        ext Ψ; rfl
    _ = (osTimeShiftLM D τ hτ).comp
          ((osSpatialRotLM D U).comp (osSpinorIdxLM D (osSpinorRotMatrix R U⁻¹))) := by
        rw [h_pt]; ext Ψ; rfl

theorem inner_osSpinorRotLM {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (hrot : OSSpinorRotCovariant R D.𝒮)
    (U : SU2) (Ψ Φ : OSPreHilbertSpace D) :
    ⟪osSpinorRotLM D U Ψ, osSpinorRotLM D U Φ⟫_ℂ = ⟪Ψ, Φ⟫_ℂ := by
  unfold osSpinorRotLM
  rw [LinearMap.comp_apply, LinearMap.comp_apply,
      inner_osSpatialRotLM_eq_osSpinorIdxLM D hrot U,
      ← LinearMap.comp_apply, ← LinearMap.comp_apply,
      osSpinorIdxLM_comp, osSpinorRotMatrix_inv_mul_self,
      osSpinorIdxLM_one, LinearMap.id_apply, LinearMap.id_apply]

theorem norm_osSpinorRotLM {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (hrot : OSSpinorRotCovariant R D.𝒮)
    (U : SU2) (Ψ : OSPreHilbertSpace D) :
    ‖osSpinorRotLM D U Ψ‖ = ‖Ψ‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ),
      inner_osSpinorRotLM D hrot U Ψ Ψ]

def osSpinorRotPreCLM {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (hrot : OSSpinorRotCovariant R D.𝒮) (U : SU2) :
    OSPreHilbertSpace D →L[ℂ] OSPreHilbertSpace D :=
  (osSpinorRotLM D U).mkContinuous 1 (fun Ψ => by
    rw [one_mul, norm_osSpinorRotLM D hrot U Ψ])

def osSpinorRot {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (hrot : OSSpinorRotCovariant R D.𝒮) (U : SU2) :
    OSHilbert D →L[ℂ] OSHilbert D :=
  (osSpinorRotPreCLM D hrot U).completion

@[simp]
lemma osSpinorRot_toOSHilbert {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (hrot : OSSpinorRotCovariant R D.𝒮)
    (U : SU2) (Ψ : OSPreHilbertSpace D) :
    osSpinorRot D hrot U (toOSHilbert D Ψ) =
      toOSHilbert D (osSpinorRotLM D U Ψ) :=
  ContinuousLinearMap.completion_apply_coe (osSpinorRotPreCLM D hrot U) Ψ

theorem inner_osSpinorRot {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (hrot : OSSpinorRotCovariant R D.𝒮)
    (U : SU2) (x y : OSHilbert D) :
    ⟪osSpinorRot D hrot U x, osSpinorRot D hrot U y⟫_ℂ = ⟪x, y⟫_ℂ := by
  induction x, y using UniformSpace.Completion.induction_on₂ with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih Ψ Φ =>
    change ⟪osSpinorRot D hrot U (toOSHilbert D Ψ),
        osSpinorRot D hrot U (toOSHilbert D Φ)⟫_ℂ =
      ⟪toOSHilbert D Ψ, toOSHilbert D Φ⟫_ℂ
    rw [osSpinorRot_toOSHilbert, osSpinorRot_toOSHilbert,
        inner_toOSHilbert, inner_toOSHilbert, inner_osSpinorRotLM D hrot U Ψ Φ]

@[simp]
theorem norm_osSpinorRot {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (hrot : OSSpinorRotCovariant R D.𝒮)
    (U : SU2) (x : OSHilbert D) :
    ‖osSpinorRot D hrot U x‖ = ‖x‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ),
      inner_osSpinorRot D hrot U x x]

@[simp]
theorem osSpinorRot_one {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (hrot : OSSpinorRotCovariant R D.𝒮) :
    osSpinorRot D hrot 1 = ContinuousLinearMap.id ℂ (OSHilbert D) := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih Ψ =>
    change osSpinorRot D hrot 1 (toOSHilbert D Ψ) = toOSHilbert D Ψ
    rw [osSpinorRot_toOSHilbert, osSpinorRotLM_one, LinearMap.id_apply]

theorem osSpinorRot_mul {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (hrot : OSSpinorRotCovariant R D.𝒮)
    (U₁ U₂ : SU2) :
    osSpinorRot D hrot (U₁ * U₂) =
      (osSpinorRot D hrot U₁).comp (osSpinorRot D hrot U₂) := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih Ψ =>
    change osSpinorRot D hrot (U₁ * U₂) (toOSHilbert D Ψ) =
      osSpinorRot D hrot U₁ (osSpinorRot D hrot U₂ (toOSHilbert D Ψ))
    rw [osSpinorRot_toOSHilbert, osSpinorRot_toOSHilbert, osSpinorRot_toOSHilbert,
        osSpinorRotLM_mul, LinearMap.comp_apply]

@[simp]
theorem osSpinorRot_inv_comp {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (hrot : OSSpinorRotCovariant R D.𝒮) (U : SU2) :
    (osSpinorRot D hrot U⁻¹).comp (osSpinorRot D hrot U) =
      ContinuousLinearMap.id ℂ (OSHilbert D) := by
  rw [← osSpinorRot_mul, inv_mul_cancel, osSpinorRot_one]

@[simp]
theorem osSpinorRot_comp_inv {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (hrot : OSSpinorRotCovariant R D.𝒮) (U : SU2) :
    (osSpinorRot D hrot U).comp (osSpinorRot D hrot U⁻¹) =
      ContinuousLinearMap.id ℂ (OSHilbert D) := by
  rw [← osSpinorRot_mul, mul_inv_cancel, osSpinorRot_one]

@[simp]
theorem osSpinorRot_osVacuum {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (hrot : OSSpinorRotCovariant R D.𝒮) (U : SU2) :
    osSpinorRot D hrot U (osVacuum D) = osVacuum D := by
  dsimp [osVacuum]
  rw [osSpinorRot_toOSHilbert, osSpinorRotLM_osVacuumPre]

theorem osSpinorRot_negOneSU2_osBasis {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (hrot : OSSpinorRotCovariant R D.𝒮)
    {ε : ℂ} (hε : R.HasSpinParity ε) (A : OSConfig ι) :
    osSpinorRot D hrot negOneSU2 (osBasis D A) = (ε ^ A.1) • osBasis D A := by
  dsimp [osBasis]
  rw [osSpinorRot_toOSHilbert, osSpinorRotLM_negOneSU2_osBasisPre D hε A, map_smul]

theorem osSpinorRot_comm_osContractionSemigroup
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (hrot : OSSpinorRotCovariant R D.𝒮)
    (hcontr : OSContractionCondition D) (U : SU2) (τ : ℝ) (hτ : 0 ≤ τ) :
    (osSpinorRot D hrot U).comp (osContractionSemigroup D hcontr τ hτ) =
      (osContractionSemigroup D hcontr τ hτ).comp (osSpinorRot D hrot U) := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih Ψ =>
    change osSpinorRot D hrot U (osContractionSemigroup D hcontr τ hτ (toOSHilbert D Ψ)) =
      osContractionSemigroup D hcontr τ hτ (osSpinorRot D hrot U (toOSHilbert D Ψ))
    rw [osContractionSemigroup_toOSHilbert, osSpinorRot_toOSHilbert,
        osSpinorRot_toOSHilbert, osContractionSemigroup_toOSHilbert,
        ← LinearMap.comp_apply, ← LinearMap.comp_apply,
        osSpinorRotLM_comm_osTimeShiftLM]

theorem osSpinorRot_eq_osSpatialRot_of_matrix_eq_one
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (hrot : OSSpinorRotCovariant R D.𝒮)
    (hscalar : OSScalarRotInvariant D.𝒮) (U : SU2)
    (hU : osSpinorRotMatrix R U⁻¹ = 1) :
    osSpinorRot D hrot U = osSpatialRot D hscalar U := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih Ψ =>
    change osSpinorRot D hrot U (toOSHilbert D Ψ) =
      osSpatialRot D hscalar U (toOSHilbert D Ψ)
    rw [osSpinorRot_toOSHilbert, osSpatialRot_toOSHilbert]
    congr 1
    unfold osSpinorRotLM
    rw [hU, osSpinorIdxLM_one, LinearMap.comp_id]

theorem osKernel_osVacuumConfig_left {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    (𝒮 : SchwingerFamily ι) (A : OSConfig ι) :
    osKernel S 𝒮 (osVacuumConfig ι) A = 𝒮 A.1 A.2.1 A.2.2.val := by
  rcases A with ⟨n, α, x, hx⟩
  unfold osKernel osVacuumConfig
  dsimp only
  rw [Finset.univ_unique, Finset.sum_singleton]
  have h_prod : (∏ i : Fin 0, S.C (Fin.elim0 i) ((default : Fin 0 → ι) i)) = 1 :=
    Finset.prod_eq_one (fun i _ => Fin.elim0 i)
  rw [h_prod, one_mul]
  rw [← schwinger_congr_n 𝒮 (Nat.zero_add n).symm]
  congr 1
  · ext i
    have hi : finCongr (Nat.zero_add n).symm i = Fin.natAdd 0 i := by ext; simp
    rw [Function.comp_apply, hi, osConcatIdx_natAdd]
  · ext i μ
    have hi : finCongr (Nat.zero_add n).symm i = Fin.natAdd 0 i := by ext; simp
    rw [Function.comp_apply, hi, osConcatPoint_natAdd]

@[simp]
theorem inner_osVacuumPre_osBasisPre {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (A : OSConfig ι) :
    ⟪osVacuumPre D, osBasisPre D A⟫_ℂ = D.𝒮 A.1 A.2.1 A.2.2.val := by
  unfold osVacuumPre
  rw [inner_osBasisPre, osKernel_osVacuumConfig_left]

@[simp]
theorem inner_osVacuum_osBasis {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (A : OSConfig ι) :
    ⟪osVacuum D, osBasis D A⟫_ℂ = D.𝒮 A.1 A.2.1 A.2.2.val := by
  dsimp [osVacuum, osBasis]
  rw [inner_toOSHilbert, inner_osVacuumPre_osBasisPre]

def osPrependPoint (n : ℕ) (x₀ : Fin 4 → ℝ) (x : Fin n → Fin 4 → ℝ) :
    Fin (n + 1) → Fin 4 → ℝ :=
  Fin.cons x₀ (fun i => x i + euclidTimeVec (x₀ 0))

lemma osPrependPoint_mem_posOrderedEuclidN (n : ℕ) {x₀ : Fin 4 → ℝ} (hx₀ : 0 < x₀ 0)
    {x : Fin n → Fin 4 → ℝ} (hx : x ∈ posOrderedEuclidN n) :
    osPrependPoint n x₀ x ∈ posOrderedEuclidN (n + 1) := by
  refine ⟨fun i => ?_, fun i hi => ?_⟩
  · refine Fin.cases ?_ (fun j => ?_) i
    · simpa [osPrependPoint] using hx₀
    · simp only [osPrependPoint, Fin.cons_succ, Pi.add_apply, euclidTimeVec, ↓reduceIte]
      linarith [hx.1 j]
  · revert hi
    refine Fin.cases ?_ (fun j => ?_) i
    · intro hi
      have h0 : 0 < n := by
        change 0 + 1 < n + 1 at hi
        omega
      have h1 : (⟨(0 : Fin (n + 1)).val + 1, hi⟩ : Fin (n + 1)) =
          Fin.succ ⟨0, h0⟩ := by ext; rfl
      rw [h1]
      simp only [osPrependPoint, Fin.cons_zero, Fin.cons_succ, Pi.add_apply,
        euclidTimeVec, ↓reduceIte]
      linarith [hx.1 ⟨0, h0⟩]
    · intro hi
      have hj : j.val + 1 < n := by
        change j.val + 1 + 1 < n + 1 at hi
        omega
      have h1 : (⟨(Fin.succ j).val + 1, hi⟩ : Fin (n + 1)) =
          Fin.succ ⟨j.val + 1, hj⟩ := by ext; rfl
      rw [h1]
      simp only [osPrependPoint, Fin.cons_succ, Pi.add_apply, euclidTimeVec, ↓reduceIte]
      linarith [hx.2 j hj]

lemma osPrependPoint_euclidRotN_su2Conj (n : ℕ) (U : SU2)
    (x₀ : Fin 4 → ℝ) (x : Fin n → Fin 4 → ℝ) :
    euclidRotN (n + 1) U (su2Conj U) (osPrependPoint n x₀ x) =
      osPrependPoint n (euclidRotApply U (su2Conj U) x₀)
        (euclidRotN n U (su2Conj U) x) := by
  ext i μ
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [osPrependPoint, euclidRotN, Fin.cons_zero, euclidRotOfSU2_mulVec]
  · simp only [osPrependPoint, euclidRotN, Fin.cons_succ, euclidRotOfSU2_mulVec,
      euclidRotApply_add, euclidRotApply_su2Conj_euclidTimeVec, euclidRotApply_su2Conj_time]

omit [Fintype ι] [DecidableEq ι] in
def osFieldPrependConfig (α₀ : ι) (x₀ : Fin 4 → ℝ) (hx₀ : 0 < x₀ 0) (A : OSConfig ι) :
    OSConfig ι :=
  ⟨A.1 + 1, (Fin.cons α₀ A.2.1,
    ⟨osPrependPoint A.1 x₀ A.2.2.val,
      osPrependPoint_mem_posOrderedEuclidN A.1 hx₀ A.2.2.property⟩)⟩

omit [Fintype ι] [DecidableEq ι] in
lemma osConfigPointRot_osFieldPrependConfig (U : SU2)
    (α₀ : ι) (x₀ : Fin 4 → ℝ) (hx₀ : 0 < x₀ 0) (A : OSConfig ι) :
    osConfigPointRot U (osFieldPrependConfig α₀ x₀ hx₀ A) =
      osFieldPrependConfig α₀ (euclidRotApply U (su2Conj U) x₀)
        (by rw [euclidRotApply_su2Conj_time]; exact hx₀)
        (osConfigPointRot U A) := by
  rcases A with ⟨n, α, x⟩
  dsimp [osFieldPrependConfig]
  rw [osConfigPointRot_mk, osConfigPointRot_mk]
  apply osConfig_mk_eq_of_val_eq
  exact osPrependPoint_euclidRotN_su2Conj n U x₀ x.val

def osFieldPrependLM {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (α₀ : ι) (x₀ : Fin 4 → ℝ) (hx₀ : 0 < x₀ 0) :
    OSPreHilbertSpace D →ₗ[ℂ] OSPreHilbertSpace D :=
  osLiftConfigMap D (osFieldPrependConfig α₀ x₀ hx₀)

theorem osSpatialRotLM_comp_osFieldPrependLM
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (U : SU2)
    (α₀ : ι) (x₀ : Fin 4 → ℝ) (hx₀ : 0 < x₀ 0) :
    (osSpatialRotLM D U).comp (osFieldPrependLM D α₀ x₀ hx₀) =
      (osFieldPrependLM D α₀ (euclidRotApply U (su2Conj U) x₀)
        (by rw [euclidRotApply_su2Conj_time]; exact hx₀)).comp
        (osSpatialRotLM D U) := by
  unfold osSpatialRotLM osFieldPrependLM
  rw [← osLiftConfigMap_comp, ← osLiftConfigMap_comp]
  congr 1
  ext A : 1
  exact osConfigPointRot_osFieldPrependConfig U α₀ x₀ hx₀ A

@[simp]
theorem inner_osVacuumPre_osFieldPrependLM_osBasisPre
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (α₀ : ι) (x₀ : Fin 4 → ℝ) (hx₀ : 0 < x₀ 0)
    (A : OSConfig ι) :
    ⟪osVacuumPre D, osFieldPrependLM D α₀ x₀ hx₀ (osBasisPre D A)⟫_ℂ =
      D.𝒮 (A.1 + 1) (Fin.cons α₀ A.2.1) (osPrependPoint A.1 x₀ A.2.2.val) := by
  unfold osFieldPrependLM
  rw [osLiftConfigMap_osBasisPre, inner_osVacuumPre_osBasisPre]
  rfl

def finConsEquiv (n : ℕ) (ι : Type*) : (ι × (Fin n → ι)) ≃ (Fin (n + 1) → ι) where
  toFun p := Fin.cons p.1 p.2
  invFun δ := (δ 0, Fin.tail δ)
  left_inv p := by
    rcases p with ⟨b, δ⟩
    simp
  right_inv δ := Fin.cons_self_tail δ

theorem osSpinorIdxLM_osFieldPrependLM
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (M : Matrix ι ι ℂ)
    (α₀ : ι) (x₀ : Fin 4 → ℝ) (hx₀ : 0 < x₀ 0) (Ψ : OSPreHilbertSpace D) :
    osSpinorIdxLM D M (osFieldPrependLM D α₀ x₀ hx₀ Ψ) =
      ∑ β₀ : ι, M α₀ β₀ • osFieldPrependLM D β₀ x₀ hx₀ (osSpinorIdxLM D M Ψ) := by
  have h_eq : (osSpinorIdxLM D M).comp (osFieldPrependLM D α₀ x₀ hx₀) =
      ∑ β₀ : ι, M α₀ β₀ • ((osFieldPrependLM D β₀ x₀ hx₀).comp (osSpinorIdxLM D M)) := by
    apply osPreHilbert_linearMap_ext
    intro A
    rcases A with ⟨n, α, x⟩
    rw [LinearMap.comp_apply]
    unfold osFieldPrependLM
    rw [osLiftConfigMap_osBasisPre, osSpinorIdxLM_osBasisPre]
    unfold osSpinorIdxSingle osFieldPrependConfig
    dsimp only [osConfigSetIdx]
    rw [← (finConsEquiv n ι).sum_comp, Fintype.sum_prod_type]
    rw [LinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun β₀ _ => ?_)
    rw [LinearMap.smul_apply, LinearMap.comp_apply, osSpinorIdxLM_osBasisPre]
    unfold osSpinorIdxSingle
    rw [map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun δ' _ => ?_)
    rw [map_smul, osLiftConfigMap_osBasisPre, smul_smul]
    congr 1
    dsimp [finConsEquiv]
    rw [Fin.prod_univ_succ]
    simp
  have h1 := LinearMap.congr_fun h_eq Ψ
  simpa [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply] using h1

theorem osSpinorRotLM_osFieldPrependLM
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (U : SU2)
    (α₀ : ι) (x₀ : Fin 4 → ℝ) (hx₀ : 0 < x₀ 0) (Ψ : OSPreHilbertSpace D) :
    osSpinorRotLM D U (osFieldPrependLM D α₀ x₀ hx₀ Ψ) =
      ∑ β₀ : ι, osSpinorRotMatrix R U⁻¹ α₀ β₀ •
        osFieldPrependLM D β₀ (euclidRotApply U (su2Conj U) x₀)
          (by rw [euclidRotApply_su2Conj_time]; exact hx₀)
          (osSpinorRotLM D U Ψ) := by
  unfold osSpinorRotLM
  rw [LinearMap.comp_apply, osSpinorIdxLM_osFieldPrependLM, map_sum]
  refine Finset.sum_congr rfl (fun β₀ _ => ?_)
  rw [map_smul]
  congr 1
  rw [← LinearMap.comp_apply, osSpatialRotLM_comp_osFieldPrependLM,
      LinearMap.comp_apply, LinearMap.comp_apply]

namespace OSReconstructedWightman

variable {R : HolomorphicLorentzRep ι} {S : StarStructure R}
  {η : ℂ} {𝒮 : SchwingerFamily ι}

abbrev osData (P : OSReconstructedWightman R S η 𝒮) : OSReflectionPositiveData R S :=
  P.osAxioms.toReflectionPositiveData

abbrev Hilbert (P : OSReconstructedWightman R S η 𝒮) : Type _ :=
  OSHilbert P.osData

def vacuum (P : OSReconstructedWightman R S η 𝒮) : P.Hilbert :=
  osVacuum P.osData

def spinorRot (P : OSReconstructedWightman R S η 𝒮) (U : SU2) :
    P.Hilbert →L[ℂ] P.Hilbert :=
  osSpinorRot P.osData P.osAxioms.osSpinorRotCovariant U

theorem inner_spinorRot (P : OSReconstructedWightman R S η 𝒮) (U : SU2)
    (x y : P.Hilbert) :
    ⟪P.spinorRot U x, P.spinorRot U y⟫_ℂ = ⟪x, y⟫_ℂ :=
  inner_osSpinorRot P.osData P.osAxioms.osSpinorRotCovariant U x y

@[simp]
theorem spinorRot_one (P : OSReconstructedWightman R S η 𝒮) :
    P.spinorRot 1 = ContinuousLinearMap.id ℂ P.Hilbert :=
  osSpinorRot_one P.osData P.osAxioms.osSpinorRotCovariant

theorem spinorRot_mul (P : OSReconstructedWightman R S η 𝒮) (U₁ U₂ : SU2) :
    P.spinorRot (U₁ * U₂) = (P.spinorRot U₁).comp (P.spinorRot U₂) :=
  osSpinorRot_mul P.osData P.osAxioms.osSpinorRotCovariant U₁ U₂

@[simp]
theorem spinorRot_vacuum (P : OSReconstructedWightman R S η 𝒮) (U : SU2) :
    P.spinorRot U P.vacuum = P.vacuum :=
  osSpinorRot_osVacuum P.osData P.osAxioms.osSpinorRotCovariant U

theorem spinorRot_negOneSU2_osBasis (P : OSReconstructedWightman R S η 𝒮)
    {ε : ℂ} (hε : R.HasSpinParity ε) (A : OSConfig ι) :
    P.spinorRot negOneSU2 (osBasis P.osData A) = (ε ^ A.1) • osBasis P.osData A :=
  osSpinorRot_negOneSU2_osBasis P.osData P.osAxioms.osSpinorRotCovariant hε A

@[simp]
theorem inner_vacuum_osBasis (P : OSReconstructedWightman R S η 𝒮) (A : OSConfig ι) :
    ⟪P.vacuum, osBasis P.osData A⟫_ℂ = 𝒮 A.1 A.2.1 A.2.2.val :=
  inner_osVacuum_osBasis P.osData A

end OSReconstructedWightman

lemma one_add_mul_two_pow_le_pow_two_pow {δ : ℝ} (hδ : 0 ≤ δ) (m : ℕ) :
    1 + (2 : ℝ) ^ m * δ ≤ (1 + δ) ^ (2 ^ m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ (2 : ℝ) m, pow_succ 2 m, pow_mul]
    have h1 : 0 ≤ 1 + (2 : ℝ) ^ m * δ := by positivity
    have h_sq : (1 + (2 : ℝ) ^ m * δ) ^ 2 ≤ ((1 + δ) ^ (2 ^ m)) ^ 2 :=
      pow_le_pow_left₀ h1 ih 2
    refine le_trans ?_ h_sq
    have h_nonneg : 0 ≤ ((2 : ℝ) ^ m * δ) ^ 2 := sq_nonneg _
    linarith

lemma exists_lt_mul_pow_two_pow {c r : ℝ} (hc : 0 < c) (hr : 1 < r) (C : ℝ) :
    ∃ m : ℕ, C < c * r ^ (2 ^ m) := by
  have hδ : 0 < r - 1 := sub_pos.mpr hr
  obtain ⟨N, hN⟩ := exists_nat_gt ((C / c - 1) / (r - 1))
  use N
  have hN_le : (N : ℝ) ≤ (2 : ℝ) ^ N := by
    exact_mod_cast Nat.le_of_lt Nat.lt_two_pow_self
  have h1 : C / c - 1 < (N : ℝ) * (r - 1) := (div_lt_iff₀ hδ).mp hN
  have h2 : (N : ℝ) * (r - 1) ≤ (2 : ℝ) ^ N * (r - 1) :=
    mul_le_mul_of_nonneg_right hN_le hδ.le
  have h3 : C / c < 1 + (2 : ℝ) ^ N * (r - 1) := by linarith
  have h4 : 1 + (2 : ℝ) ^ N * (r - 1) ≤ r ^ (2 ^ N) := by
    have := one_add_mul_two_pow_le_pow_two_pow hδ.le N
    rwa [add_sub_cancel] at this
  have h5 : C / c < r ^ (2 ^ N) := lt_of_lt_of_le h3 h4
  have h6 := (div_lt_iff₀ hc).mp h5
  linarith

theorem le_of_pow_two_pow_le_mul_subexponential {a b : ℝ} (hb : 0 ≤ b)
    {M : ℕ → ℝ} (h_iter : ∀ m : ℕ, a ^ (2 ^ m) ≤ b ^ (2 ^ m - 1) * M m)
    (h_subexp : ∀ c > 0, ∀ r > 1, ∃ m : ℕ, M m < c * r ^ (2 ^ m)) :
    a ≤ b := by
  by_contra h_lt
  push Not at h_lt
  rcases eq_or_lt_of_le hb with rfl | hb_pos
  · have h1 := h_iter 1
    norm_num at h1
    linarith
  · have hr : 1 < a / b := (one_lt_div hb_pos).mpr h_lt
    obtain ⟨m, hm⟩ := h_subexp b hb_pos (a / b) hr
    have h_pos_b : 0 < b ^ (2 ^ m - 1) := pow_pos hb_pos _
    have h_step := h_iter m
    have h_strict : b ^ (2 ^ m - 1) * M m < b ^ (2 ^ m - 1) * (b * (a / b) ^ (2 ^ m)) :=
      mul_lt_mul_of_pos_left hm h_pos_b
    have h_id : b ^ (2 ^ m - 1) * (b * (a / b) ^ (2 ^ m)) = a ^ (2 ^ m) := by
      rw [← mul_assoc, ← pow_succ, div_pow]
      have h_exp : 2 ^ m - 1 + 1 = 2 ^ m := Nat.sub_add_cancel Nat.one_le_two_pow
      rw [h_exp, mul_div_cancel₀ _ (ne_of_gt (pow_pos hb_pos (2 ^ m)))]
    rw [h_id] at h_strict
    linarith

theorem le_of_pow_two_pow_le_mul_const {a b C : ℝ} (hb : 0 ≤ b)
    (h_iter : ∀ m : ℕ, a ^ (2 ^ m) ≤ b ^ (2 ^ m - 1) * C) :
    a ≤ b :=
  le_of_pow_two_pow_le_mul_subexponential hb h_iter
    (fun _ hc _ hr => exists_lt_mul_pow_two_pow hc hr C)

def OSTimeShiftSubexponential {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) : Prop :=
  ∀ (τ : ℝ) (hτ : 0 ≤ τ) (Ψ : OSPreHilbertSpace D),
    ∀ c > 0, ∀ r > 1, ∃ m : ℕ,
      ‖osTimeShiftLM D ((2 : ℝ) ^ m * τ) (mul_nonneg (by positivity) hτ) Ψ‖ <
        c * r ^ (2 ^ m)

def OSTimeShiftBounded {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) : Prop :=
  ∀ Ψ : OSPreHilbertSpace D, ∃ C : ℝ, ∀ (τ : ℝ) (hτ : 0 ≤ τ),
    ‖osTimeShiftLM D τ hτ Ψ‖ ≤ C

def OSBasisTimeShiftBounded {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) : Prop :=
  ∀ A : OSConfig ι, ∃ C : ℝ, ∀ (τ : ℝ) (hτ : 0 ≤ τ),
    ‖osTimeShiftLM D τ hτ (osBasisPre D A)‖ ≤ C

def OSDiagonalKernelBounded {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    (𝒮 : SchwingerFamily ι) : Prop :=
  ∀ A : OSConfig ι, ∃ C : ℝ, ∀ (τ : ℝ) (hτ : 0 ≤ τ),
    ‖osKernel S 𝒮 (osConfigTimeShift τ hτ A) (osConfigTimeShift τ hτ A)‖ ≤ C

lemma OSTimeShiftBounded.toSubexponential {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {D : OSReflectionPositiveData R S} (h : OSTimeShiftBounded D) :
    OSTimeShiftSubexponential D := by
  intro τ hτ Ψ c hc r hr
  obtain ⟨C, hC⟩ := h Ψ
  obtain ⟨m, hm⟩ := exists_lt_mul_pow_two_pow hc hr C
  exact ⟨m, lt_of_le_of_lt (hC ((2 : ℝ) ^ m * τ) (mul_nonneg (by positivity) hτ)) hm⟩

lemma OSBasisTimeShiftBounded.toTimeShiftBounded
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {D : OSReflectionPositiveData R S} (h : OSBasisTimeShiftBounded D) :
    OSTimeShiftBounded D := by
  intro Ψ
  choose C hC using h
  refine ⟨∑ A ∈ Ψ.toFinsupp.support, ‖Ψ.toFinsupp A‖ * C A, fun τ hτ => ?_⟩
  have hΨ : osTimeShiftLM D τ hτ Ψ =
      ∑ A ∈ Ψ.toFinsupp.support, Ψ.toFinsupp A • osTimeShiftLM D τ hτ (osBasisPre D A) := by
    conv_lhs => rw [osPreHilbert_eq_finsupp_sum_osBasisPre D Ψ]
    rw [map_finsuppSum]
    unfold Finsupp.sum
    refine Finset.sum_congr rfl (fun A _ => (osTimeShiftLM D τ hτ).map_smul _ _)
  rw [hΨ]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun A _ => ?_))
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (hC A τ hτ) (norm_nonneg _)

lemma OSDiagonalKernelBounded.toBasisTimeShiftBounded
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (h : OSDiagonalKernelBounded S D.𝒮) :
    OSBasisTimeShiftBounded D := by
  intro A
  obtain ⟨C, hC⟩ := h A
  refine ⟨Real.sqrt C, fun τ hτ => ?_⟩
  unfold osTimeShiftLM
  rw [osLiftConfigMap_osBasisPre, norm_eq_sqrt_re_inner (𝕜 := ℂ), inner_osBasisPre]
  apply Real.sqrt_le_sqrt
  exact le_trans (RCLike.re_le_norm _) (hC τ hτ)

theorem osContractionCondition_of_subexponential
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (htrans : OSTranslationInvariant D.𝒮)
    (hsub : OSTimeShiftSubexponential D) :
    OSContractionCondition D := by
  intro τ hτ Ψ
  exact le_of_pow_two_pow_le_mul_subexponential (norm_nonneg _)
    (fun m => norm_pow_two_pow_osTimeShiftLM_le D htrans m τ hτ Ψ)
    (hsub τ hτ Ψ)

theorem osContractionCondition_of_bounded
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (htrans : OSTranslationInvariant D.𝒮)
    (hbdd : OSTimeShiftBounded D) :
    OSContractionCondition D :=
  osContractionCondition_of_subexponential D htrans hbdd.toSubexponential

theorem osContractionCondition_of_basisBounded
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (htrans : OSTranslationInvariant D.𝒮)
    (hbdd : OSBasisTimeShiftBounded D) :
    OSContractionCondition D :=
  osContractionCondition_of_bounded D htrans hbdd.toTimeShiftBounded

theorem osContractionCondition_of_diagonalKernelBounded
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (htrans : OSTranslationInvariant D.𝒮)
    (hbdd : OSDiagonalKernelBounded S D.𝒮) :
    OSContractionCondition D :=
  osContractionCondition_of_basisBounded D htrans (hbdd.toBasisTimeShiftBounded D)

def OSVacuumNormalized (𝒮 : SchwingerFamily ι) : Prop :=
  𝒮 0 Fin.elim0 (euclidOrderedBasePoint 0) = 1

@[simp]
theorem inner_osVacuumPre_self {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) :
    ⟪osVacuumPre D, osVacuumPre D⟫_ℂ = D.𝒮 0 Fin.elim0 (euclidOrderedBasePoint 0) :=
  inner_osVacuumPre_osBasisPre D (osVacuumConfig ι)

@[simp]
theorem inner_osVacuum_self {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) :
    ⟪osVacuum D, osVacuum D⟫_ℂ = D.𝒮 0 Fin.elim0 (euclidOrderedBasePoint 0) :=
  inner_osVacuum_osBasis D (osVacuumConfig ι)

theorem inner_osVacuum_self_of_normalized {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (hnorm : OSVacuumNormalized D.𝒮) :
    ⟪osVacuum D, osVacuum D⟫_ℂ = 1 := by
  rw [inner_osVacuum_self, hnorm]

theorem norm_osVacuum_of_normalized {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (hnorm : OSVacuumNormalized D.𝒮) :
    ‖osVacuum D‖ = 1 := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), inner_osVacuum_self_of_normalized D hnorm]
  simp

@[simp]
theorem inner_osBasisPre_osVacuumPre {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (A : OSConfig ι) :
    ⟪osBasisPre D A, osVacuumPre D⟫_ℂ = star (D.𝒮 A.1 A.2.1 A.2.2.val) := by
  rw [← inner_conj_symm, inner_osVacuumPre_osBasisPre]
  rfl

@[simp]
theorem inner_osBasis_osVacuum {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (A : OSConfig ι) :
    ⟪osBasis D A, osVacuum D⟫_ℂ = star (D.𝒮 A.1 A.2.1 A.2.2.val) := by
  rw [← inner_conj_symm, inner_osVacuum_osBasis]
  rfl

lemma inner_osPreHilbert_osVacuumPre_left {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (Φ : OSPreHilbertSpace D) :
    ⟪osVacuumPre D, Φ⟫_ℂ =
      Φ.toFinsupp.sum (fun B cB => cB * osKernel S D.𝒮 (osVacuumConfig ι) B) := by
  change osPreInner S D.𝒮 (Finsupp.single (osVacuumConfig ι) 1) Φ.toFinsupp = _
  unfold osPreInner
  simp

lemma inner_osPreHilbert_osVacuumPre_right {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (Ψ : OSPreHilbertSpace D) :
    ⟪Ψ, osVacuumPre D⟫_ℂ =
      Ψ.toFinsupp.sum (fun A cA => star cA * osKernel S D.𝒮 A (osVacuumConfig ι)) := by
  change osPreInner S D.𝒮 Ψ.toFinsupp (Finsupp.single (osVacuumConfig ι) 1) = _
  unfold osPreInner
  refine Finsupp.sum_congr (fun A _ => ?_)
  simp

lemma inner_osVacuumPre_mul_inner_eq_finsupp_sum
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (Ψ Φ : OSPreHilbertSpace D) :
    ⟪Ψ, osVacuumPre D⟫_ℂ * ⟪osVacuumPre D, Φ⟫_ℂ =
      Ψ.toFinsupp.sum (fun A cA =>
        Φ.toFinsupp.sum (fun B cB =>
          star cA * cB *
            (osKernel S D.𝒮 A (osVacuumConfig ι) *
              osKernel S D.𝒮 (osVacuumConfig ι) B))) := by
  rw [inner_osPreHilbert_osVacuumPre_right, inner_osPreHilbert_osVacuumPre_left,
      Finsupp.sum_mul]
  refine Finsupp.sum_congr (fun A _ => ?_)
  rw [Finsupp.mul_sum]
  refine Finsupp.sum_congr (fun B _ => ?_)
  ring

@[simp]
theorem norm_osSpatialTranslate {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (htrans : OSTranslationInvariant D.𝒮)
    (a : Fin 3 → ℝ) (x : OSHilbert D) :
    ‖osSpatialTranslate D htrans a x‖ = ‖x‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ),
      inner_osSpatialTranslate D htrans a x x]

@[simp]
theorem osSpatialTranslate_neg_comp {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (htrans : OSTranslationInvariant D.𝒮)
    (a : Fin 3 → ℝ) :
    (osSpatialTranslate D htrans (-a)).comp (osSpatialTranslate D htrans a) =
      ContinuousLinearMap.id ℂ (OSHilbert D) := by
  rw [← osSpatialTranslate_add, neg_add_cancel, osSpatialTranslate_zero]

@[simp]
theorem osSpatialTranslate_comp_neg {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (htrans : OSTranslationInvariant D.𝒮)
    (a : Fin 3 → ℝ) :
    (osSpatialTranslate D htrans a).comp (osSpatialTranslate D htrans (-a)) =
      ContinuousLinearMap.id ℂ (OSHilbert D) := by
  rw [← osSpatialTranslate_add, add_neg_cancel, osSpatialTranslate_zero]

def OSTimeClusterDecomposition {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) : Prop :=
  ∀ A B : OSConfig ι,
    Tendsto
      (fun τ : ℝ =>
        osKernel S D.𝒮 A (osConfigTimeShift (max τ 0) (le_max_right τ 0) B))
      atTop
      (𝓝 (osKernel S D.𝒮 A (osVacuumConfig ι) *
        osKernel S D.𝒮 (osVacuumConfig ι) B))

def OSSpatialClusterAlong {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (a : Fin 3 → ℝ) : Prop :=
  ∀ A B : OSConfig ι,
    Tendsto
      (fun t : ℝ =>
        osKernel S D.𝒮 A (osConfigSpatialShift (t • a) B))
      atTop
      (𝓝 (osKernel S D.𝒮 A (osVacuumConfig ι) *
        osKernel S D.𝒮 (osVacuumConfig ι) B))

def OSSpatialClusterDecomposition {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) : Prop :=
  ∀ a : Fin 3 → ℝ, a ≠ 0 → OSSpatialClusterAlong D a

theorem tendsto_inner_osTimeShiftLM_atTop
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (hcluster : OSTimeClusterDecomposition D)
    (Ψ Φ : OSPreHilbertSpace D) :
    Tendsto
      (fun τ : ℝ =>
        ⟪Ψ, osTimeShiftLM D (max τ 0) (le_max_right τ 0) Φ⟫_ℂ)
      atTop
      (𝓝 (⟪Ψ, osVacuumPre D⟫_ℂ * ⟪osVacuumPre D, Φ⟫_ℂ)) := by
  have h_eq : (fun τ : ℝ => ⟪Ψ, osTimeShiftLM D (max τ 0) (le_max_right τ 0) Φ⟫_ℂ) =
      fun τ : ℝ =>
        Ψ.toFinsupp.sum (fun A cA =>
          Φ.toFinsupp.sum (fun B cB =>
            star cA * cB *
              osKernel S D.𝒮 A (osConfigTimeShift (max τ 0) (le_max_right τ 0) B))) := by
    ext τ
    unfold osTimeShiftLM
    have hR := inner_osLiftConfigMap D id (osConfigTimeShift (max τ 0) (le_max_right τ 0)) Ψ Φ
    rw [osLiftConfigMap_id, LinearMap.id_apply] at hR
    exact hR
  rw [h_eq, inner_osVacuumPre_mul_inner_eq_finsupp_sum]
  unfold Finsupp.sum
  refine tendsto_finsetSum _ (fun A _ => ?_)
  refine tendsto_finsetSum _ (fun B _ => ?_)
  exact Tendsto.const_mul (star (Ψ.toFinsupp A) * Φ.toFinsupp B) (hcluster A B)

theorem tendsto_inner_osSpatialTranslateLM_atTop
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) {a : Fin 3 → ℝ}
    (hcluster : OSSpatialClusterAlong D a)
    (Ψ Φ : OSPreHilbertSpace D) :
    Tendsto
      (fun t : ℝ =>
        ⟪Ψ, osSpatialTranslateLM D (t • a) Φ⟫_ℂ)
      atTop
      (𝓝 (⟪Ψ, osVacuumPre D⟫_ℂ * ⟪osVacuumPre D, Φ⟫_ℂ)) := by
  have h_eq : (fun t : ℝ => ⟪Ψ, osSpatialTranslateLM D (t • a) Φ⟫_ℂ) =
      fun t : ℝ =>
        Ψ.toFinsupp.sum (fun A cA =>
          Φ.toFinsupp.sum (fun B cB =>
            star cA * cB *
              osKernel S D.𝒮 A (osConfigSpatialShift (t • a) B))) := by
    ext t
    unfold osSpatialTranslateLM
    have hR := inner_osLiftConfigMap D id (osConfigSpatialShift (t • a)) Ψ Φ
    rw [osLiftConfigMap_id, LinearMap.id_apply] at hR
    exact hR
  rw [h_eq, inner_osVacuumPre_mul_inner_eq_finsupp_sum]
  unfold Finsupp.sum
  refine tendsto_finsetSum _ (fun A _ => ?_)
  refine tendsto_finsetSum _ (fun B _ => ?_)
  exact Tendsto.const_mul (star (Ψ.toFinsupp A) * Φ.toFinsupp B) (hcluster A B)

lemma tendsto_of_forall_pos_exists_approx {f : ℝ → ℂ} {L : ℂ}
    (h : ∀ δ > 0, ∃ (g : ℝ → ℂ) (L' : ℂ),
      Tendsto g atTop (𝓝 L') ∧ (∀ t : ℝ, ‖f t - g t‖ ≤ δ) ∧ ‖L' - L‖ ≤ δ) :
    Tendsto f atTop (𝓝 L) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨g, L', hg, hfg, hLL'⟩ := h (ε / 3) (by linarith)
  have hg' := (Metric.tendsto_nhds.mp hg) (ε / 3) (by linarith)
  filter_upwards [hg'] with t ht
  rw [dist_eq_norm] at ht ⊢
  have h_eq : f t - L = (f t - g t) + (g t - L') + (L' - L) := by ring
  have h_tri1 := norm_add_le ((f t - g t) + (g t - L')) (L' - L)
  have h_tri2 := norm_add_le (f t - g t) (g t - L')
  rw [h_eq]
  linarith [hfg t]

theorem tendsto_inner_completion_of_norm_le_one
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S)
    (T : ℝ → OSHilbert D →L[ℂ] OSHilbert D)
    (hT_norm : ∀ (t : ℝ) (z : OSHilbert D), ‖T t z‖ ≤ ‖z‖)
    (hT_dense : ∀ Ψ Φ : OSPreHilbertSpace D,
      Tendsto (fun t : ℝ => ⟪toOSHilbert D Ψ, T t (toOSHilbert D Φ)⟫_ℂ)
        atTop (𝓝 (⟪toOSHilbert D Ψ, osVacuum D⟫_ℂ * ⟪osVacuum D, toOSHilbert D Φ⟫_ℂ)))
    (x y : OSHilbert D) :
    Tendsto (fun t : ℝ => ⟪x, T t y⟫_ℂ)
      atTop (𝓝 (⟪x, osVacuum D⟫_ℂ * ⟪osVacuum D, y⟫_ℂ)) := by
  have h_dense : DenseRange (toOSHilbert D) := UniformSpace.Completion.denseRange_coe
  have h_step1 : ∀ Ψ : OSPreHilbertSpace D,
      Tendsto (fun t : ℝ => ⟪toOSHilbert D Ψ, T t y⟫_ℂ)
        atTop (𝓝 (⟪toOSHilbert D Ψ, osVacuum D⟫_ℂ * ⟪osVacuum D, y⟫_ℂ)) := by
    intro Ψ
    apply tendsto_of_forall_pos_exists_approx
    intro δ hδ
    let M : ℝ := max (‖toOSHilbert D Ψ‖) (‖toOSHilbert D Ψ‖ * ‖osVacuum D‖ * ‖osVacuum D‖) + 1
    have hM_pos : 0 < M := by positivity
    obtain ⟨_, ⟨Φ, rfl⟩, hΦ⟩ := Metric.mem_closure_iff.mp (h_dense y) (δ / M) (div_pos hδ hM_pos)
    rw [dist_eq_norm] at hΦ
    refine ⟨fun t => ⟪toOSHilbert D Ψ, T t (toOSHilbert D Φ)⟫_ℂ,
      ⟪toOSHilbert D Ψ, osVacuum D⟫_ℂ * ⟪osVacuum D, toOSHilbert D Φ⟫_ℂ,
      hT_dense Ψ Φ, fun t => ?_, ?_⟩
    · have h_sub : ⟪toOSHilbert D Ψ, T t y⟫_ℂ - ⟪toOSHilbert D Ψ, T t (toOSHilbert D Φ)⟫_ℂ =
          ⟪toOSHilbert D Ψ, T t (y - toOSHilbert D Φ)⟫_ℂ := by
        rw [← inner_sub_right, map_sub]
      rw [h_sub]
      have h1 : ‖⟪toOSHilbert D Ψ, T t (y - toOSHilbert D Φ)⟫_ℂ‖ ≤
          ‖toOSHilbert D Ψ‖ * ‖y - toOSHilbert D Φ‖ := by
        refine le_trans (norm_inner_le_norm _ _) ?_
        exact mul_le_mul_of_nonneg_left (hT_norm t (y - toOSHilbert D Φ)) (norm_nonneg _)
      have h2 : ‖toOSHilbert D Ψ‖ ≤ M := by
        dsimp [M]
        linarith [le_max_left (‖toOSHilbert D Ψ‖)
          (‖toOSHilbert D Ψ‖ * ‖osVacuum D‖ * ‖osVacuum D‖)]
      have h3 : ‖toOSHilbert D Ψ‖ * ‖y - toOSHilbert D Φ‖ ≤ M * (δ / M) :=
        mul_le_mul h2 hΦ.le (norm_nonneg _) hM_pos.le
      rw [mul_div_cancel₀ _ (ne_of_gt hM_pos)] at h3
      exact le_trans h1 h3
    · have h_sub : ⟪toOSHilbert D Ψ, osVacuum D⟫_ℂ * ⟪osVacuum D, toOSHilbert D Φ⟫_ℂ -
          ⟪toOSHilbert D Ψ, osVacuum D⟫_ℂ * ⟪osVacuum D, y⟫_ℂ =
          ⟪toOSHilbert D Ψ, osVacuum D⟫_ℂ * ⟪osVacuum D, toOSHilbert D Φ - y⟫_ℂ := by
        rw [← mul_sub, inner_sub_right]
      rw [h_sub, norm_mul]
      have ha := norm_inner_le_norm (𝕜 := ℂ) (toOSHilbert D Ψ) (osVacuum D)
      have hb := norm_inner_le_norm (𝕜 := ℂ) (osVacuum D) (toOSHilbert D Φ - y)
      rw [norm_sub_rev] at hb
      have h1 : ‖⟪toOSHilbert D Ψ, osVacuum D⟫_ℂ‖ * ‖⟪osVacuum D, toOSHilbert D Φ - y⟫_ℂ‖ ≤
          (‖toOSHilbert D Ψ‖ * ‖osVacuum D‖ * ‖osVacuum D‖) * ‖y - toOSHilbert D Φ‖ := by
        calc ‖⟪toOSHilbert D Ψ, osVacuum D⟫_ℂ‖ * ‖⟪osVacuum D, toOSHilbert D Φ - y⟫_ℂ‖
          _ ≤ (‖toOSHilbert D Ψ‖ * ‖osVacuum D‖) * (‖osVacuum D‖ * ‖y - toOSHilbert D Φ‖) :=
            mul_le_mul ha hb (norm_nonneg _) (by positivity)
          _ = (‖toOSHilbert D Ψ‖ * ‖osVacuum D‖ * ‖osVacuum D‖) * ‖y - toOSHilbert D Φ‖ := by
            ring
      have h2 : ‖toOSHilbert D Ψ‖ * ‖osVacuum D‖ * ‖osVacuum D‖ ≤ M := by
        dsimp [M]
        linarith [le_max_right (‖toOSHilbert D Ψ‖)
          (‖toOSHilbert D Ψ‖ * ‖osVacuum D‖ * ‖osVacuum D‖)]
      have h3 : (‖toOSHilbert D Ψ‖ * ‖osVacuum D‖ * ‖osVacuum D‖) * ‖y - toOSHilbert D Φ‖ ≤
          M * (δ / M) :=
        mul_le_mul h2 hΦ.le (norm_nonneg _) hM_pos.le
      rw [mul_div_cancel₀ _ (ne_of_gt hM_pos)] at h3
      exact le_trans h1 h3
  apply tendsto_of_forall_pos_exists_approx
  intro δ hδ
  let M : ℝ := max (‖y‖) (‖osVacuum D‖ * ‖osVacuum D‖ * ‖y‖) + 1
  have hM_pos : 0 < M := by positivity
  obtain ⟨_, ⟨Ψ, rfl⟩, hΨ⟩ := Metric.mem_closure_iff.mp (h_dense x) (δ / M) (div_pos hδ hM_pos)
  rw [dist_eq_norm] at hΨ
  refine ⟨fun t => ⟪toOSHilbert D Ψ, T t y⟫_ℂ,
    ⟪toOSHilbert D Ψ, osVacuum D⟫_ℂ * ⟪osVacuum D, y⟫_ℂ,
    h_step1 Ψ, fun t => ?_, ?_⟩
  · have h_sub : ⟪x, T t y⟫_ℂ - ⟪toOSHilbert D Ψ, T t y⟫_ℂ =
        ⟪x - toOSHilbert D Ψ, T t y⟫_ℂ := (inner_sub_left _ _ _).symm
    rw [h_sub]
    have h1 : ‖⟪x - toOSHilbert D Ψ, T t y⟫_ℂ‖ ≤ ‖x - toOSHilbert D Ψ‖ * ‖y‖ := by
      refine le_trans (norm_inner_le_norm (𝕜 := ℂ) _ _) ?_
      exact mul_le_mul_of_nonneg_left (hT_norm t y) (norm_nonneg _)
    have h2 : ‖y‖ ≤ M := by
      dsimp [M]
      linarith [le_max_left (‖y‖) (‖osVacuum D‖ * ‖osVacuum D‖ * ‖y‖)]
    have h3 : ‖x - toOSHilbert D Ψ‖ * ‖y‖ ≤ (δ / M) * M :=
      mul_le_mul hΨ.le h2 (norm_nonneg _) (by positivity)
    rw [div_mul_cancel₀ _ (ne_of_gt hM_pos)] at h3
    exact le_trans h1 h3
  · have h_sub : ⟪toOSHilbert D Ψ, osVacuum D⟫_ℂ * ⟪osVacuum D, y⟫_ℂ -
        ⟪x, osVacuum D⟫_ℂ * ⟪osVacuum D, y⟫_ℂ =
        ⟪toOSHilbert D Ψ - x, osVacuum D⟫_ℂ * ⟪osVacuum D, y⟫_ℂ := by
      rw [← sub_mul, inner_sub_left]
    rw [h_sub, norm_mul]
    have ha := norm_inner_le_norm (𝕜 := ℂ) (toOSHilbert D Ψ - x) (osVacuum D)
    rw [norm_sub_rev] at ha
    have hb := norm_inner_le_norm (𝕜 := ℂ) (osVacuum D) y
    have h1 : ‖⟪toOSHilbert D Ψ - x, osVacuum D⟫_ℂ‖ * ‖⟪osVacuum D, y⟫_ℂ‖ ≤
        ‖x - toOSHilbert D Ψ‖ * (‖osVacuum D‖ * ‖osVacuum D‖ * ‖y‖) := by
      calc ‖⟪toOSHilbert D Ψ - x, osVacuum D⟫_ℂ‖ * ‖⟪osVacuum D, y⟫_ℂ‖
        _ ≤ (‖x - toOSHilbert D Ψ‖ * ‖osVacuum D‖) * (‖osVacuum D‖ * ‖y‖) :=
          mul_le_mul ha hb (norm_nonneg _) (by positivity)
        _ = ‖x - toOSHilbert D Ψ‖ * (‖osVacuum D‖ * ‖osVacuum D‖ * ‖y‖) := by ring
    have h2 : ‖osVacuum D‖ * ‖osVacuum D‖ * ‖y‖ ≤ M := by
      dsimp [M]
      linarith [le_max_right (‖y‖) (‖osVacuum D‖ * ‖osVacuum D‖ * ‖y‖)]
    have h3 : ‖x - toOSHilbert D Ψ‖ * (‖osVacuum D‖ * ‖osVacuum D‖ * ‖y‖) ≤
        (δ / M) * M :=
      mul_le_mul hΨ.le h2 (by positivity) (by positivity)
    rw [div_mul_cancel₀ _ (ne_of_gt hM_pos)] at h3
    exact le_trans h1 h3

theorem tendsto_inner_osContractionSemigroup_atTop
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (hcontr : OSContractionCondition D)
    (hcluster : OSTimeClusterDecomposition D)
    (x y : OSHilbert D) :
    Tendsto
      (fun τ : ℝ =>
        ⟪x, osContractionSemigroup D hcontr (max τ 0) (le_max_right τ 0) y⟫_ℂ)
      atTop
      (𝓝 (⟪x, osVacuum D⟫_ℂ * ⟪osVacuum D, y⟫_ℂ)) := by
  refine tendsto_inner_completion_of_norm_le_one D
    (fun τ => osContractionSemigroup D hcontr (max τ 0) (le_max_right τ 0))
    (fun τ z => norm_osContractionSemigroup_le D hcontr (max τ 0) (le_max_right τ 0) z)
    (fun Ψ Φ => ?_) x y
  dsimp [osVacuum]
  rw [inner_toOSHilbert, inner_toOSHilbert]
  have h_eq : (fun t : ℝ =>
      ⟪toOSHilbert D Ψ,
        osContractionSemigroup D hcontr (max t 0) (le_max_right t 0) (toOSHilbert D Φ)⟫_ℂ) =
      fun t : ℝ => ⟪Ψ, osTimeShiftLM D (max t 0) (le_max_right t 0) Φ⟫_ℂ := by
    ext t
    rw [osContractionSemigroup_toOSHilbert, inner_toOSHilbert]
  rw [h_eq]
  exact tendsto_inner_osTimeShiftLM_atTop D hcluster Ψ Φ

theorem tendsto_inner_osSpatialTranslate_atTop
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (htrans : OSTranslationInvariant D.𝒮)
    {a : Fin 3 → ℝ} (hcluster : OSSpatialClusterAlong D a)
    (x y : OSHilbert D) :
    Tendsto
      (fun t : ℝ =>
        ⟪x, osSpatialTranslate D htrans (t • a) y⟫_ℂ)
      atTop
      (𝓝 (⟪x, osVacuum D⟫_ℂ * ⟪osVacuum D, y⟫_ℂ)) := by
  refine tendsto_inner_completion_of_norm_le_one D
    (fun t => osSpatialTranslate D htrans (t • a))
    (fun t z => (norm_osSpatialTranslate D htrans (t • a) z).le)
    (fun Ψ Φ => ?_) x y
  dsimp [osVacuum]
  rw [inner_toOSHilbert, inner_toOSHilbert]
  have h_eq : (fun t : ℝ =>
      ⟪toOSHilbert D Ψ, osSpatialTranslate D htrans (t • a) (toOSHilbert D Φ)⟫_ℂ) =
      fun t : ℝ => ⟪Ψ, osSpatialTranslateLM D (t • a) Φ⟫_ℂ := by
    ext t
    rw [osSpatialTranslate_toOSHilbert, inner_toOSHilbert]
  rw [h_eq]
  exact tendsto_inner_osSpatialTranslateLM_atTop D hcluster Ψ Φ

theorem osTimeShiftSubexponential_of_timeCluster
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (htrans : OSTranslationInvariant D.𝒮)
    (hcluster : OSTimeClusterDecomposition D) :
    OSTimeShiftSubexponential D := by
  intro τ hτ Ψ c hc r hr
  rcases eq_or_lt_of_le hτ with rfl | hτ_pos
  · obtain ⟨m, hm⟩ := exists_lt_mul_pow_two_pow hc hr ‖Ψ‖
    refine ⟨m, ?_⟩
    have h0 : osTimeShiftLM D ((2 : ℝ) ^ m * 0) (mul_nonneg (by positivity) le_rfl) Ψ = Ψ := by
      have h_eq : osTimeShiftLM D ((2 : ℝ) ^ m * 0) (mul_nonneg (by positivity) le_rfl) =
          osTimeShiftLM D 0 le_rfl := by congr 2; ring
      rw [h_eq, osTimeShiftLM_zero, LinearMap.id_apply]
    rwa [h0]
  · let L : ℂ := ⟪Ψ, osVacuumPre D⟫_ℂ * ⟪osVacuumPre D, Ψ⟫_ℂ
    have h_tendsto := tendsto_inner_osTimeShiftLM_atTop D hcluster Ψ Ψ
    have h_ev := (Metric.tendsto_nhds.mp h_tendsto) 1 zero_lt_one
    rw [Filter.eventually_atTop] at h_ev
    obtain ⟨S₀, hS₀⟩ := h_ev
    obtain ⟨N₁, hN₁⟩ := exists_nat_gt (S₀ / (2 * τ))
    obtain ⟨N₂, hN₂⟩ := exists_lt_mul_pow_two_pow hc hr (Real.sqrt (‖L‖ + 1))
    let m : ℕ := max N₁ N₂
    refine ⟨m, ?_⟩
    have hm1 : N₁ ≤ m := le_max_left N₁ N₂
    have hm2 : N₂ ≤ m := le_max_right N₁ N₂
    have h_sm : S₀ ≤ 2 * ((2 : ℝ) ^ m * τ) := by
      have h_lt : (N₁ : ℝ) < (2 : ℝ) ^ m := by
        calc (N₁ : ℝ)
          _ ≤ (m : ℝ) := by exact_mod_cast hm1
          _ < (2 : ℝ) ^ m := by exact_mod_cast Nat.lt_two_pow_self
      have h_div : S₀ < (N₁ : ℝ) * (2 * τ) := (div_lt_iff₀ (by positivity)).mp hN₁
      have h_le : (N₁ : ℝ) * (2 * τ) ≤ (2 : ℝ) ^ m * (2 * τ) :=
        mul_le_mul_of_nonneg_right h_lt.le (by positivity)
      linarith
    have h_dist := hS₀ (2 * ((2 : ℝ) ^ m * τ)) h_sm
    rw [dist_eq_norm] at h_dist
    have h_max : max (2 * ((2 : ℝ) ^ m * τ)) 0 = 2 * ((2 : ℝ) ^ m * τ) :=
      max_eq_left (by positivity)
    have h_norm_inner :
        ‖⟪Ψ, osTimeShiftLM D (2 * ((2 : ℝ) ^ m * τ)) (by positivity) Ψ⟫_ℂ‖ ≤ ‖L‖ + 1 := by
      have h_congr : osTimeShiftLM D (max (2 * ((2 : ℝ) ^ m * τ)) 0)
          (le_max_right (2 * ((2 : ℝ) ^ m * τ)) 0) Ψ =
          osTimeShiftLM D (2 * ((2 : ℝ) ^ m * τ)) (by positivity) Ψ := by
        congr 2
      rw [h_congr] at h_dist
      have h_tri := norm_add_le
        (⟪Ψ, osTimeShiftLM D (2 * ((2 : ℝ) ^ m * τ)) (by positivity) Ψ⟫_ℂ - L) L
      rw [sub_add_cancel] at h_tri
      linarith
    have h_sq : ‖osTimeShiftLM D ((2 : ℝ) ^ m * τ) (mul_nonneg (by positivity) hτ) Ψ‖ ^ 2 ≤
        ‖L‖ + 1 := by
      have h_id : ‖osTimeShiftLM D ((2 : ℝ) ^ m * τ) (mul_nonneg (by positivity) hτ) Ψ‖ ^ 2 =
          RCLike.re ⟪Ψ, osTimeShiftLM D (2 * ((2 : ℝ) ^ m * τ)) (by positivity) Ψ⟫_ℂ := by
        rw [← osTimeShiftLM_isSymmetric D htrans (2 * ((2 : ℝ) ^ m * τ)) (by positivity) Ψ Ψ]
        rw [inner_osTimeShiftLM_self_eq_norm_sq_half D htrans
          (2 * ((2 : ℝ) ^ m * τ)) (by positivity) Ψ]
        have h_half : osTimeShiftLM D (2 * ((2 : ℝ) ^ m * τ) / 2) (by positivity) Ψ =
            osTimeShiftLM D ((2 : ℝ) ^ m * τ) (mul_nonneg (by positivity) hτ) Ψ := by
          congr 2
          ring
        rw [h_half]
        norm_cast
      rw [h_id]
      exact le_trans (RCLike.re_le_norm _) h_norm_inner
    have h_le_sqrt :
        ‖osTimeShiftLM D ((2 : ℝ) ^ m * τ) (mul_nonneg (by positivity) hτ) Ψ‖ ≤
          Real.sqrt (‖L‖ + 1) := by
      rw [← Real.sqrt_sq (norm_nonneg _)]
      exact Real.sqrt_le_sqrt h_sq
    have h_pow_mono : c * r ^ (2 ^ N₂) ≤ c * r ^ (2 ^ m) := by
      apply mul_le_mul_of_nonneg_left _ hc.le
      exact pow_le_pow_right₀ hr.le (Nat.pow_le_pow_right (by norm_num) hm2)
    exact lt_of_le_of_lt h_le_sqrt (lt_of_lt_of_le hN₂ h_pow_mono)

theorem osContractionCondition_of_timeCluster
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (htrans : OSTranslationInvariant D.𝒮)
    (hcluster : OSTimeClusterDecomposition D) :
    OSContractionCondition D :=
  osContractionCondition_of_subexponential D htrans
    (osTimeShiftSubexponential_of_timeCluster D htrans hcluster)

theorem eq_smul_osVacuum_of_osContractionSemigroup_fixed
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (hcontr : OSContractionCondition D)
    (hcluster : OSTimeClusterDecomposition D)
    {Ψ : OSHilbert D}
    (hfixed : ∀ (τ : ℝ) (hτ : 0 ≤ τ),
      osContractionSemigroup D hcontr τ hτ Ψ = Ψ) :
    Ψ = ⟪osVacuum D, Ψ⟫_ℂ • osVacuum D := by
  have h_inner_eq : ∀ x : OSHilbert D,
      ⟪x, Ψ⟫_ℂ = ⟪x, ⟪osVacuum D, Ψ⟫_ℂ • osVacuum D⟫_ℂ := by
    intro x
    have h_tendsto := tendsto_inner_osContractionSemigroup_atTop D hcontr hcluster x Ψ
    have h_const_fn : (fun τ : ℝ =>
        ⟪x, osContractionSemigroup D hcontr (max τ 0) (le_max_right τ 0) Ψ⟫_ℂ) =
        fun _ : ℝ => ⟪x, Ψ⟫_ℂ := by
      ext τ
      rw [hfixed (max τ 0) (le_max_right τ 0)]
    rw [h_const_fn] at h_tendsto
    have h_lim : ⟪x, Ψ⟫_ℂ = ⟪x, osVacuum D⟫_ℂ * ⟪osVacuum D, Ψ⟫_ℂ :=
      tendsto_nhds_unique tendsto_const_nhds h_tendsto
    rw [h_lim, inner_smul_right, mul_comm]
  have h_diff : ⟪Ψ - ⟪osVacuum D, Ψ⟫_ℂ • osVacuum D,
      Ψ - ⟪osVacuum D, Ψ⟫_ℂ • osVacuum D⟫_ℂ = 0 := by
    rw [inner_sub_right, h_inner_eq (Ψ - ⟪osVacuum D, Ψ⟫_ℂ • osVacuum D), sub_self]
  exact sub_eq_zero.mp (inner_self_eq_zero.mp h_diff)

theorem eq_zero_of_osContractionSemigroup_fixed_of_inner_osVacuum_eq_zero
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (hcontr : OSContractionCondition D)
    (hcluster : OSTimeClusterDecomposition D)
    {Ψ : OSHilbert D}
    (hfixed : ∀ (τ : ℝ) (hτ : 0 ≤ τ),
      osContractionSemigroup D hcontr τ hτ Ψ = Ψ)
    (horth : ⟪osVacuum D, Ψ⟫_ℂ = 0) :
    Ψ = 0 := by
  rw [eq_smul_osVacuum_of_osContractionSemigroup_fixed D hcontr hcluster hfixed,
      horth, zero_smul]

theorem eq_smul_osVacuum_of_osSpatialTranslate_fixed
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (htrans : OSTranslationInvariant D.𝒮)
    {a : Fin 3 → ℝ} (hcluster : OSSpatialClusterAlong D a)
    {Ψ : OSHilbert D}
    (hfixed : ∀ t : ℝ, osSpatialTranslate D htrans (t • a) Ψ = Ψ) :
    Ψ = ⟪osVacuum D, Ψ⟫_ℂ • osVacuum D := by
  have h_inner_eq : ∀ x : OSHilbert D,
      ⟪x, Ψ⟫_ℂ = ⟪x, ⟪osVacuum D, Ψ⟫_ℂ • osVacuum D⟫_ℂ := by
    intro x
    have h_tendsto := tendsto_inner_osSpatialTranslate_atTop D htrans hcluster x Ψ
    have h_const_fn : (fun t : ℝ =>
        ⟪x, osSpatialTranslate D htrans (t • a) Ψ⟫_ℂ) =
        fun _ : ℝ => ⟪x, Ψ⟫_ℂ := by
      ext t
      rw [hfixed t]
    rw [h_const_fn] at h_tendsto
    have h_lim : ⟪x, Ψ⟫_ℂ = ⟪x, osVacuum D⟫_ℂ * ⟪osVacuum D, Ψ⟫_ℂ :=
      tendsto_nhds_unique tendsto_const_nhds h_tendsto
    rw [h_lim, inner_smul_right, mul_comm]
  have h_diff : ⟪Ψ - ⟪osVacuum D, Ψ⟫_ℂ • osVacuum D,
      Ψ - ⟪osVacuum D, Ψ⟫_ℂ • osVacuum D⟫_ℂ = 0 := by
    rw [inner_sub_right, h_inner_eq (Ψ - ⟪osVacuum D, Ψ⟫_ℂ • osVacuum D), sub_self]
  exact sub_eq_zero.mp (inner_self_eq_zero.mp h_diff)

theorem eq_zero_of_osSpatialTranslate_fixed_of_inner_osVacuum_eq_zero
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (htrans : OSTranslationInvariant D.𝒮)
    {a : Fin 3 → ℝ} (hcluster : OSSpatialClusterAlong D a)
    {Ψ : OSHilbert D}
    (hfixed : ∀ t : ℝ, osSpatialTranslate D htrans (t • a) Ψ = Ψ)
    (horth : ⟪osVacuum D, Ψ⟫_ℂ = 0) :
    Ψ = 0 := by
  rw [eq_smul_osVacuum_of_osSpatialTranslate_fixed D htrans hcluster hfixed,
      horth, zero_smul]

theorem tendsto_inner_osContractionSemigroup_eq_zero_of_inner_osVacuum_eq_zero
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (hcontr : OSContractionCondition D)
    (hcluster : OSTimeClusterDecomposition D)
    (x : OSHilbert D) {y : OSHilbert D} (horth : ⟪osVacuum D, y⟫_ℂ = 0) :
    Tendsto
      (fun τ : ℝ =>
        ⟪x, osContractionSemigroup D hcontr (max τ 0) (le_max_right τ 0) y⟫_ℂ)
      atTop (𝓝 0) := by
  have h := tendsto_inner_osContractionSemigroup_atTop D hcontr hcluster x y
  rwa [horth, mul_zero] at h

theorem tendsto_inner_osSpatialTranslate_eq_zero_of_inner_osVacuum_eq_zero
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (htrans : OSTranslationInvariant D.𝒮)
    {a : Fin 3 → ℝ} (hcluster : OSSpatialClusterAlong D a)
    (x : OSHilbert D) {y : OSHilbert D} (horth : ⟪osVacuum D, y⟫_ℂ = 0) :
    Tendsto
      (fun t : ℝ => ⟪x, osSpatialTranslate D htrans (t • a) y⟫_ℂ)
      atTop (𝓝 0) := by
  have h := tendsto_inner_osSpatialTranslate_atTop D htrans hcluster x y
  rwa [horth, mul_zero] at h

namespace OSReconstructedWightman

variable {R : HolomorphicLorentzRep ι} {S : StarStructure R}
  {η : ℂ} {𝒮 : SchwingerFamily ι}

def spatialTranslate (P : OSReconstructedWightman R S η 𝒮) (a : Fin 3 → ℝ) :
    P.Hilbert →L[ℂ] P.Hilbert :=
  osSpatialTranslate P.osData P.osAxioms.os1_translation a

def timeContraction (P : OSReconstructedWightman R S η 𝒮) (τ : ℝ) (hτ : 0 ≤ τ) :
    P.Hilbert →L[ℂ] P.Hilbert :=
  osContractionSemigroup P.osData P.contraction τ hτ

theorem norm_vacuum_of_normalized (P : OSReconstructedWightman R S η 𝒮)
    (hnorm : OSVacuumNormalized 𝒮) :
    ‖P.vacuum‖ = 1 :=
  norm_osVacuum_of_normalized P.osData hnorm

theorem vacuum_unique_of_timeCluster (P : OSReconstructedWightman R S η 𝒮)
    (hcluster : OSTimeClusterDecomposition P.osData)
    {Ψ : P.Hilbert}
    (hfixed : ∀ (τ : ℝ) (hτ : 0 ≤ τ), P.timeContraction τ hτ Ψ = Ψ) :
    Ψ = ⟪P.vacuum, Ψ⟫_ℂ • P.vacuum :=
  eq_smul_osVacuum_of_osContractionSemigroup_fixed P.osData P.contraction hcluster hfixed

theorem vacuum_unique_of_spatialCluster (P : OSReconstructedWightman R S η 𝒮)
    {a : Fin 3 → ℝ} (hcluster : OSSpatialClusterAlong P.osData a)
    {Ψ : P.Hilbert}
    (hfixed : ∀ t : ℝ, P.spatialTranslate (t • a) Ψ = Ψ) :
    Ψ = ⟪P.vacuum, Ψ⟫_ℂ • P.vacuum :=
  eq_smul_osVacuum_of_osSpatialTranslate_fixed P.osData P.osAxioms.os1_translation hcluster hfixed

end OSReconstructedWightman

lemma mem_forward_tube_one (z : Fin 1 → Fin 4 → ℂ) : z ∈ forward_tube_n 1 := by
  intro i hi
  omega

lemma mem_orderedEuclidN_one (x : Fin 1 → Fin 4 → ℝ) : x ∈ orderedEuclidN 1 := by
  intro i hi
  omega

lemma shift_mem_forward_tube_n (n : ℕ) {z : Fin n → Fin 4 → ℂ}
    (hz : z ∈ forward_tube_n n) (a : Fin 4 → ℂ) :
    (fun i => z i + a) ∈ forward_tube_n n := by
  intro i hi
  have h_diff : (fun i => z i + a) i - (fun i => z i + a) ⟨i.val + 1, hi⟩ =
      z i - z ⟨i.val + 1, hi⟩ :=
    add_sub_add_right_eq_sub (z i) (z ⟨i.val + 1, hi⟩) a
  change (fun k : Fin 4 => -((((fun i => z i + a) i -
    (fun i => z i + a) ⟨i.val + 1, hi⟩) k).im)) ∈ forward_light_cone
  rw [h_diff]
  exact hz i hi

def diagShiftCLM (n : ℕ) : (Fin 4 → ℂ) →L[ℂ] (Fin n → Fin 4 → ℂ) :=
  ContinuousLinearMap.pi (fun _ : Fin n => ContinuousLinearMap.id ℂ (Fin 4 → ℂ))

@[simp]
lemma diagShiftCLM_apply (n : ℕ) (a : Fin 4 → ℂ) (i : Fin n) :
    diagShiftCLM n a i = a := rfl

lemma analyticOn_forward_tube_shift (n : ℕ) {f : (Fin n → Fin 4 → ℂ) → ℂ}
    (hf : AnalyticOn ℂ f (forward_tube_n n)) (a : Fin 4 → ℂ) :
    AnalyticOn ℂ (fun z => f (fun i => z i + a)) (forward_tube_n n) := by
  have h_aff : AnalyticOn ℂ (fun z : Fin n → Fin 4 → ℂ => z + fun _ => a) (forward_tube_n n) :=
    ((ContinuousLinearMap.id ℂ (Fin n → Fin 4 → ℂ)).analyticOn (forward_tube_n n)).add
      analyticOn_const
  exact hf.comp h_aff (fun z hz => shift_mem_forward_tube_n n hz a)

lemma analyticOn_univ_shift_param (n : ℕ) {f : (Fin n → Fin 4 → ℂ) → ℂ}
    (hf : AnalyticOn ℂ f (forward_tube_n n))
    {z : Fin n → Fin 4 → ℂ} (hz : z ∈ forward_tube_n n) :
    AnalyticOn ℂ (fun a : Fin 4 → ℂ => f (fun i => z i + a)) Set.univ := by
  have h_aff : AnalyticOn ℂ (fun a : Fin 4 → ℂ => z + diagShiftCLM n a) Set.univ :=
    analyticOn_const.add ((diagShiftCLM n).analyticOn Set.univ)
  exact hf.comp h_aff (fun a _ => shift_mem_forward_tube_n n hz a)

theorem analyticOn_univ_eq_of_eventuallyEq_wickEmbed
    {g₁ g₂ : (Fin 4 → ℂ) → ℂ}
    (hg₁ : AnalyticOn ℂ g₁ Set.univ) (hg₂ : AnalyticOn ℂ g₂ Set.univ)
    (x₀ : Fin 4 → ℝ)
    (h_ev : ∀ᶠ x in 𝓝 x₀, g₁ (wickEmbed x) = g₂ (wickEmbed x)) :
    ∀ a : Fin 4 → ℂ, g₁ a = g₂ a := by
  intro a
  let proj0 : (Fin 1 → Fin 4 → ℂ) →L[ℂ] (Fin 4 → ℂ) := ContinuousLinearMap.proj (0 : Fin 1)
  have hf₁ : AnalyticOn ℂ (fun w : Fin 1 → Fin 4 → ℂ => g₁ (proj0 w)) (forward_tube_n 1) :=
    hg₁.comp (proj0.analyticOn _) (fun _ _ => Set.mem_univ _)
  have hf₂ : AnalyticOn ℂ (fun w : Fin 1 → Fin 4 → ℂ => g₂ (proj0 w)) (forward_tube_n 1) :=
    hg₂.comp (proj0.analyticOn _) (fun _ _ => Set.mem_univ _)
  have h_cont : Continuous (fun y : Fin 1 → Fin 4 → ℝ => y 0) := continuous_apply 0
  have h_tendsto : Tendsto (fun y : Fin 1 → Fin 4 → ℝ => y 0) (𝓝 (fun _ => x₀)) (𝓝 x₀) :=
    h_cont.tendsto (fun _ => x₀)
  have h_ev1 : ∀ᶠ y : Fin 1 → Fin 4 → ℝ in 𝓝 (fun _ => x₀),
      g₁ (proj0 (wickEmbedN 1 y)) = g₂ (proj0 (wickEmbedN 1 y)) :=
    h_tendsto.eventually h_ev
  exact analyticOn_forward_tube_eq_of_eventuallyEq_wickEmbedN 1 hf₁ hf₂
    (mem_orderedEuclidN_one (fun _ => x₀)) h_ev1 (mem_forward_tube_one (fun _ => a))

theorem analyticOn_univ_eq_of_wickEmbed_eq
    {g₁ g₂ : (Fin 4 → ℂ) → ℂ}
    (hg₁ : AnalyticOn ℂ g₁ Set.univ) (hg₂ : AnalyticOn ℂ g₂ Set.univ)
    (h_eq : ∀ x : Fin 4 → ℝ, g₁ (wickEmbed x) = g₂ (wickEmbed x)) :
    ∀ a : Fin 4 → ℂ, g₁ a = g₂ a :=
  analyticOn_univ_eq_of_eventuallyEq_wickEmbed hg₁ hg₂ 0
    (Filter.Eventually.of_forall h_eq)

lemma wickEmbedN_shift (n : ℕ) (x : Fin n → Fin 4 → ℝ) (a : Fin 4 → ℝ) :
    wickEmbedN n (fun i => x i + a) = fun i => wickEmbedN n x i + wickEmbed a := by
  ext i μ
  exact congrFun (wickEmbed_add (x i) a) μ

omit [Fintype ι] [DecidableEq ι] in
theorem tube_wickEmbed_shift_eq_of_posOrderedEuclidN_eq {W : WightmanFamily ι}
    (E : TubeExtension W) (n : ℕ) (α : Fin n → ι) (x_a : Fin 4 → ℝ)
    (h_shift : ∀ x ∈ posOrderedEuclidN n,
      schwingerFromTube E n α (fun i => x i + x_a) = schwingerFromTube E n α x)
    (z : Fin n → Fin 4 → ℂ) (hz : z ∈ forward_tube_n n) :
    E.H n α (fun i => z i + wickEmbed x_a) = E.H n α z := by
  refine analyticOn_forward_tube_eq_of_posOrderedEuclidN_eq n
    (analyticOn_forward_tube_shift n (E.analytic n α) (wickEmbed x_a))
    (E.analytic n α) (fun x hx => ?_) hz
  change E.H n α (fun i => wickEmbedN n x i + wickEmbed x_a) = schwingerFromTube E n α x
  rw [← wickEmbedN_shift n x x_a]
  exact h_shift x hx

omit [Fintype ι] [DecidableEq ι] in
theorem tubeTranslationInvariant_of_posOrdered_posTimeShift {W : WightmanFamily ι}
    (E : TubeExtension W)
    (h_pos : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ posOrderedEuclidN n → ∀ x_a : Fin 4 → ℝ, 0 < x_a 0 →
      schwingerFromTube E n α (fun i => x i + x_a) = schwingerFromTube E n α x) :
    TubeTranslationInvariant E := by
  intro n α z a hz
  have h_open : IsOpen {x_a : Fin 4 → ℝ | 0 < x_a 0} :=
    isOpen_lt continuous_const (continuous_apply 0)
  have h_mem : euclidTimeVec 1 ∈ {x_a : Fin 4 → ℝ | 0 < x_a 0} := by
    simp [euclidTimeVec]
  apply analyticOn_univ_eq_of_eventuallyEq_wickEmbed
    (analyticOn_univ_shift_param n (E.analytic n α) hz)
    (analyticOn_const (v := E.H n α z))
    (euclidTimeVec 1) _ a
  filter_upwards [h_open.mem_nhds h_mem] with x_a hx_a
  exact tube_wickEmbed_shift_eq_of_posOrderedEuclidN_eq E n α x_a
    (fun x hx => h_pos n α x hx x_a hx_a) z hz

omit [Fintype ι] [DecidableEq ι] in
theorem tubeTranslationInvariant_of_osTranslationInvariant {W : WightmanFamily ι}
    (E : TubeExtension W) (htrans : OSTranslationInvariant (schwingerFromTube E)) :
    TubeTranslationInvariant E :=
  tubeTranslationInvariant_of_posOrdered_posTimeShift E
    (fun n α x hx x_a _ =>
      htrans n α x (posOrderedEuclidN_subset_orderedEuclidN n hx) x_a)

omit [Fintype ι] [DecidableEq ι] in
theorem tubeTranslationInvariant_iff_osTranslationInvariant {W : WightmanFamily ι}
    (E : TubeExtension W) :
    TubeTranslationInvariant E ↔ OSTranslationInvariant (schwingerFromTube E) :=
  ⟨schwingerFromTube_translation_invariant E,
   tubeTranslationInvariant_of_osTranslationInvariant E⟩

omit [Fintype ι] [DecidableEq ι] in
theorem tube_eq_sub_point_of_tubeTranslationInvariant {W : WightmanFamily ι}
    (E : TubeExtension W) (htrans : TubeTranslationInvariant E)
    (n : ℕ) (α : Fin n → ι) (z : Fin n → Fin 4 → ℂ) (hz : z ∈ forward_tube_n n)
    (k : Fin n) :
    E.H n α z = E.H n α (fun i => z i - z k) := by
  have h := (htrans n α z (-z k) hz).symm
  simpa [sub_eq_add_neg] using h

omit [Fintype ι] [DecidableEq ι] in
theorem tube_onePoint_eq_zero_eval_of_tubeTranslationInvariant {W : WightmanFamily ι}
    (E : TubeExtension W) (htrans : TubeTranslationInvariant E)
    (α : Fin 1 → ι) (z : Fin 1 → Fin 4 → ℂ) :
    E.H 1 α z = E.H 1 α 0 := by
  have h := tube_eq_sub_point_of_tubeTranslationInvariant E htrans 1 α z
    (mem_forward_tube_one z) 0
  have h0 : (fun i : Fin 1 => z i - z 0) = 0 := by
    ext i μ
    fin_cases i
    simp
  rwa [h0] at h

omit [Fintype ι] [DecidableEq ι] in
theorem osTranslationInvariant_onePoint_eq_zero_eval {𝒮 : SchwingerFamily ι}
    (htrans : OSTranslationInvariant 𝒮)
    (α : Fin 1 → ι) (x : Fin 1 → Fin 4 → ℝ) :
    𝒮 1 α x = 𝒮 1 α 0 := by
  have h := htrans 1 α x (mem_orderedEuclidN_one x) (-x 0)
  have h0 : (fun i : Fin 1 => x i + -x 0) = 0 := by
    ext i μ
    fin_cases i
    simp
  rw [h0] at h
  exact h.symm

theorem wightman_eq_zero_of_odd_fermion (R : HolomorphicLorentzRep ι)
    (W : WightmanFamily ι) (E : TubeExtension W) (hcov : TubeCovariant R E)
    (hε : R.HasSpinParity (-1))
    (n : ℕ) (hn : Odd n) (α : Fin n → ι)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    W n α f = 0 :=
  wightman_eq_zero_of_tube_eq_zero E n α
    (fun z hz => tube_eq_zero_of_odd_fermion R W E hcov hε n hn z hz α) f

namespace OSReconstructedWightman

variable {R : HolomorphicLorentzRep ι} {S : StarStructure R}
  {η : ℂ} {𝒮 : SchwingerFamily ι}

theorem osTranslationInvariant_schwingerFromTube (P : OSReconstructedWightman R S η 𝒮) :
    OSTranslationInvariant (schwingerFromTube P.E) := by
  intro n α x hx a
  have hxa : (fun i => x i + a) ∈ orderedEuclidN n :=
    shift_mem_orderedEuclidN n hx a
  rw [← P.schwinger_eq n α (fun i => x i + a) hxa,
      ← P.schwinger_eq n α x hx]
  exact P.osAxioms.os1_translation n α x hx a

theorem tube_translationInvariant (P : OSReconstructedWightman R S η 𝒮) :
    TubeTranslationInvariant P.E :=
  tubeTranslationInvariant_of_osTranslationInvariant P.E
    P.osTranslationInvariant_schwingerFromTube

theorem tube_H_shift (P : OSReconstructedWightman R S η 𝒮)
    (n : ℕ) (α : Fin n → ι) (z : Fin n → Fin 4 → ℂ) (a : Fin 4 → ℂ)
    (hz : z ∈ forward_tube_n n) :
    P.E.H n α (fun i => z i + a) = P.E.H n α z :=
  P.tube_translationInvariant n α z a hz

theorem tube_H_sub_point (P : OSReconstructedWightman R S η 𝒮)
    (n : ℕ) (α : Fin n → ι) (z : Fin n → Fin 4 → ℂ) (hz : z ∈ forward_tube_n n)
    (k : Fin n) :
    P.E.H n α z = P.E.H n α (fun i => z i - z k) :=
  tube_eq_sub_point_of_tubeTranslationInvariant P.E P.tube_translationInvariant n α z hz k

theorem tube_onePoint_eq_zero_eval (P : OSReconstructedWightman R S η 𝒮)
    (α : Fin 1 → ι) (z : Fin 1 → Fin 4 → ℂ) :
    P.E.H 1 α z = P.E.H 1 α 0 :=
  tube_onePoint_eq_zero_eval_of_tubeTranslationInvariant P.E P.tube_translationInvariant α z

theorem tube_neg_rev_two (P : OSReconstructedWightman R S η 𝒮)
    (α : Fin 2 → ι) (z : Fin 2 → Fin 4 → ℂ) (hz : z ∈ forward_tube_n 2) :
    P.E.H 2 α (-(z ∘ Fin.rev)) = P.E.H 2 α z :=
  tubeTranslationInvariant_neg_rev_two P.E P.tube_translationInvariant α z hz

theorem twoPointSpinExchange_of_subsingleton_index [Subsingleton ι]
    (P : OSReconstructedWightman R S η 𝒮) :
    TwoPointSpinExchange 1 P.E :=
  twoPointSpinExchange_of_subsingleton P.E P.tube_translationInvariant

theorem spin_statistics_of_subsingleton_unconditional [Subsingleton ι]
    (P : OSReconstructedWightman R S η 𝒮) (hε : R.HasSpinParity 1)
    (h_nondeg : ∃ (α : Fin 2 → ι) (f : SchwartzMap (Fin 2 → Fin 4 → ℝ) ℂ), P.W 2 α f ≠ 0) :
    η = 1 :=
  P.spin_statistics_of_twoPoint_ne_zero hε P.twoPointSpinExchange_of_subsingleton_index h_nondeg

theorem fermion_tube_twoPoint_diag_eq_zero
    (P : OSReconstructedWightman R S (-1) 𝒮)
    (c : ι) (z : Fin 2 → Fin 4 → ℂ) (hz : z ∈ forward_tube_n 2) :
    P.E.H 2 (fun _ => c) z = 0 :=
  _root_.QFT.fermion_tube_twoPoint_diag_eq_zero P.E P.tube_translationInvariant
    P.tube_weakLocality c z hz

theorem fermion_wightman_twoPoint_diag_eq_zero
    (P : OSReconstructedWightman R S (-1) 𝒮)
    (c : ι) (f : SchwartzMap (Fin 2 → Fin 4 → ℝ) ℂ) :
    P.W 2 (fun _ => c) f = 0 :=
  _root_.QFT.fermion_wightman_twoPoint_diag_eq_zero P.E P.tube_translationInvariant
    P.tube_weakLocality c f

theorem wightman_eq_zero_of_odd_fermion (P : OSReconstructedWightman R S η 𝒮)
    (hε : R.HasSpinParity (-1))
    (n : ℕ) (hn : Odd n) (α : Fin n → ι)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    P.W n α f = 0 :=
  _root_.QFT.wightman_eq_zero_of_odd_fermion R P.W P.E P.tube_covariant hε n hn α f

end OSReconstructedWightman

theorem osterwalder_schrader_grand_synthesis_theorem
    (R : HolomorphicLorentzRep ι) (S : StarStructure R) (η : ℂ) (𝒮 : SchwingerFamily ι)
    (P : OSReconstructedWightman R S η 𝒮) :
    TubeTranslationInvariant P.E ∧
    ComplexCovariant R P.E ∧
    WightmanPCT η R P.W ∧
    (∀ P' : OSReconstructedWightman R S η 𝒮, P'.W = P.W) ∧
    (∀ U₁ U₂ : SU2, P.spinorRot (U₁ * U₂) = (P.spinorRot U₁).comp (P.spinorRot U₂)) ∧
    (∀ U : SU2, P.spinorRot U P.vacuum = P.vacuum) ∧
    (∀ A : OSConfig ι, ⟪P.vacuum, osBasis P.osData A⟫_ℂ = 𝒮 A.1 A.2.1 A.2.2.val) ∧
    (OSTimeClusterDecomposition P.osData →
      ∀ Ψ : P.Hilbert, (∀ (τ : ℝ) (hτ : 0 ≤ τ), P.timeContraction τ hτ Ψ = Ψ) →
        Ψ = ⟪P.vacuum, Ψ⟫_ℂ • P.vacuum) :=
  ⟨P.tube_translationInvariant,
   P.complexCovariant,
   P.wightman_pct,
   fun P' => P'.wightman_unique_unconditional P,
   P.spinorRot_mul,
   P.spinorRot_vacuum,
   P.inner_vacuum_osBasis,
   fun hcluster _Ψ hfixed => P.vacuum_unique_of_timeCluster hcluster hfixed⟩

lemma orderedEuclidN_pos_of_zero_pos (j : ℕ) {y : Fin j → Fin 4 → ℝ}
    (hy : y ∈ orderedEuclidN j)
    (h0 : ∀ hj : 0 < j, 0 < y ⟨0, hj⟩ 0) :
    y ∈ posOrderedEuclidN j := by
  refine ⟨fun ⟨k, hk⟩ => ?_, hy⟩
  induction k with
  | zero => exact h0 hk
  | succ m ih =>
    have hm : m < j := Nat.lt_of_succ_lt hk
    exact lt_trans (ih hm) (hy ⟨m, hm⟩ hk)

lemma exists_timeShift_mem_posOrderedEuclidN (n : ℕ) {x : Fin n → Fin 4 → ℝ}
    (hx : x ∈ orderedEuclidN n) :
    ∃ τ : ℝ, (fun i => x i + euclidTimeVec τ) ∈ posOrderedEuclidN n := by
  by_cases hn : 0 < n
  · refine ⟨1 - x ⟨0, hn⟩ 0, orderedEuclidN_pos_of_zero_pos n
      (shift_mem_orderedEuclidN n hx (euclidTimeVec (1 - x ⟨0, hn⟩ 0))) (fun _ => ?_)⟩
    simp [euclidTimeVec]
  · refine ⟨0, orderedEuclidN_pos_of_zero_pos n
      (shift_mem_orderedEuclidN n hx (euclidTimeVec 0)) (fun h0 => (hn h0).elim)⟩

omit [Fintype ι] [DecidableEq ι] in
lemma schwinger_eq_zero_of_posOrderedEuclidN_eq_zero {𝒮 : SchwingerFamily ι}
    (htrans : OSTranslationInvariant 𝒮) (n : ℕ) (α : Fin n → ι)
    (h_pos : ∀ x ∈ posOrderedEuclidN n, 𝒮 n α x = 0)
    {x : Fin n → Fin 4 → ℝ} (hx : x ∈ orderedEuclidN n) :
    𝒮 n α x = 0 := by
  obtain ⟨τ, hτ⟩ := exists_timeShift_mem_posOrderedEuclidN n hx
  rw [← htrans n α x hx (euclidTimeVec τ)]
  exact h_pos _ hτ

def osSplitOneTimeShift (j : ℕ) (x : Fin (1 + j) → Fin 4 → ℝ) : ℝ :=
  if hj : 0 < j then
    -(x (Fin.castAdd j 0) 0 + x (Fin.natAdd 1 ⟨0, hj⟩) 0) / 2
  else
    -x (Fin.castAdd j 0) 0 - 1

def osSplitOneLeft (j : ℕ) (x : Fin (1 + j) → Fin 4 → ℝ) : Fin 1 → Fin 4 → ℝ :=
  fun _ => euclidTimeReflect (x (Fin.castAdd j 0) + euclidTimeVec (osSplitOneTimeShift j x))

def osSplitOneRight (j : ℕ) (x : Fin (1 + j) → Fin 4 → ℝ) : Fin j → Fin 4 → ℝ :=
  fun i => x (Fin.natAdd 1 i) + euclidTimeVec (osSplitOneTimeShift j x)

lemma osSplitOne_first_lt_second (j : ℕ) {x : Fin (1 + j) → Fin 4 → ℝ}
    (hx : x ∈ orderedEuclidN (1 + j)) (hj : 0 < j) :
    x (Fin.castAdd j 0) 0 < x (Fin.natAdd 1 ⟨0, hj⟩) 0 := by
  have hlt : (Fin.castAdd j (0 : Fin 1)).val + 1 < 1 + j := by
    dsimp
    omega
  have h_eq : (⟨(Fin.castAdd j (0 : Fin 1)).val + 1, hlt⟩ : Fin (1 + j)) =
      Fin.natAdd 1 ⟨0, hj⟩ := by
    ext
    rfl
  simpa [h_eq] using hx (Fin.castAdd j 0) hlt

lemma osSplitOneLeft_mem_posOrderedEuclidN (j : ℕ) {x : Fin (1 + j) → Fin 4 → ℝ}
    (hx : x ∈ orderedEuclidN (1 + j)) :
    osSplitOneLeft j x ∈ posOrderedEuclidN 1 := by
  refine ⟨fun _ => ?_, mem_orderedEuclidN_one _⟩
  simp only [osSplitOneLeft, euclidTimeReflect, Pi.add_apply, euclidTimeVec, ↓reduceIte]
  unfold osSplitOneTimeShift
  split_ifs with hj
  · have h01 := osSplitOne_first_lt_second j hx hj
    linarith
  · linarith

lemma osSplitOneRight_mem_posOrderedEuclidN (j : ℕ) {x : Fin (1 + j) → Fin 4 → ℝ}
    (hx : x ∈ orderedEuclidN (1 + j)) :
    osSplitOneRight j x ∈ posOrderedEuclidN j := by
  refine orderedEuclidN_pos_of_zero_pos j (fun i hi => ?_) (fun hj => ?_)
  · simp only [osSplitOneRight, Pi.add_apply, euclidTimeVec, ↓reduceIte]
    have hlt : (Fin.natAdd 1 i).val + 1 < 1 + j := by
      dsimp
      omega
    have h_eq : (⟨(Fin.natAdd 1 i).val + 1, hlt⟩ : Fin (1 + j)) =
        Fin.natAdd 1 ⟨i.val + 1, hi⟩ := by
      ext
      rfl
    have h_step := hx (Fin.natAdd 1 i) hlt
    rw [h_eq] at h_step
    linarith
  · simp only [osSplitOneRight, Pi.add_apply, euclidTimeVec, ↓reduceIte]
    unfold osSplitOneTimeShift
    rw [dif_pos hj]
    have h01 := osSplitOne_first_lt_second j hx hj
    linarith

theorem osConcatPoint_osSplitOne (j : ℕ) (x : Fin (1 + j) → Fin 4 → ℝ) :
    osConcatPoint 1 j (osSplitOneLeft j x) (osSplitOneRight j x) =
      fun m => x m + euclidTimeVec (osSplitOneTimeShift j x) := by
  ext m μ
  by_cases hm : m.val < 1
  · have h_eq : m = Fin.castAdd j 0 := by
      ext
      dsimp
      omega
    rw [h_eq, osConcatPoint_castAdd]
    exact congrFun (euclidTimeReflect_involutive _) μ
  · have h_ge : 1 ≤ m.val := by omega
    have h_eq : m = Fin.natAdd 1 ⟨m.val - 1, Nat.sub_lt_left_of_lt_add h_ge m.isLt⟩ := by
      ext
      dsimp
      omega
    rw [h_eq, osConcatPoint_natAdd]
    rfl

omit [Fintype ι] [DecidableEq ι] in
lemma osConcatIdx_one_left (j : ℕ) (α : Fin (1 + j) → ι) :
    osConcatIdx 1 j (fun _ => α (Fin.castAdd j 0)) (fun i => α (Fin.natAdd 1 i)) = α := by
  ext m
  by_cases hm : m.val < 1
  · have h_eq : m = Fin.castAdd j 0 := by
      ext
      dsimp
      omega
    rw [h_eq, osConcatIdx_castAdd]
  · have h_ge : 1 ≤ m.val := by omega
    have h_eq : m = Fin.natAdd 1 ⟨m.val - 1, Nat.sub_lt_left_of_lt_add h_ge m.isLt⟩ := by
      ext
      dsimp
      omega
    rw [h_eq, osConcatIdx_natAdd]

omit [Fintype ι] [DecidableEq ι] in
def osSplitOneLeftConfig (j : ℕ) (c : ι) (x : Fin (1 + j) → Fin 4 → ℝ)
    (hx : x ∈ orderedEuclidN (1 + j)) : OSConfig ι :=
  ⟨1, (fun _ => c, ⟨osSplitOneLeft j x, osSplitOneLeft_mem_posOrderedEuclidN j hx⟩)⟩

omit [Fintype ι] [DecidableEq ι] in
def osSplitOneRightConfig (j : ℕ) (α : Fin (1 + j) → ι) (x : Fin (1 + j) → Fin 4 → ℝ)
    (hx : x ∈ orderedEuclidN (1 + j)) : OSConfig ι :=
  ⟨j, (fun i => α (Fin.natAdd 1 i),
    ⟨osSplitOneRight j x, osSplitOneRight_mem_posOrderedEuclidN j hx⟩)⟩

theorem schwinger_one_add_eq_sum_osKernel
    {R : HolomorphicLorentzRep ι} (S : StarStructure R) (𝒮 : SchwingerFamily ι)
    (htrans : OSTranslationInvariant 𝒮)
    (j : ℕ) (α : Fin (1 + j) → ι) {x : Fin (1 + j) → Fin 4 → ℝ}
    (hx : x ∈ orderedEuclidN (1 + j)) :
    𝒮 (1 + j) α x =
      ∑ c : ι, star (S.C (α (Fin.castAdd j 0)) c) *
        osKernel S 𝒮 (osSplitOneLeftConfig j c x hx) (osSplitOneRightConfig j α x hx) := by
  have h_kern : ∀ c : ι,
      osKernel S 𝒮 (osSplitOneLeftConfig j c x hx) (osSplitOneRightConfig j α x hx) =
        ∑ β : Fin 1 → ι, S.C c (β 0) *
          𝒮 (1 + j) (osConcatIdx 1 j β (fun i => α (Fin.natAdd 1 i)))
            (osConcatPoint 1 j (osSplitOneLeft j x) (osSplitOneRight j x)) := by
    intro c
    unfold osKernel osSplitOneLeftConfig osSplitOneRightConfig
    dsimp only
    refine Finset.sum_congr rfl (fun β _ => ?_)
    rw [Fin.prod_univ_one]
  simp_rw [h_kern, Finset.mul_sum]
  rw [Finset.sum_comm]
  have h_collapse : ∀ β : Fin 1 → ι,
      (∑ c : ι, star (S.C (α (Fin.castAdd j 0)) c) *
        (S.C c (β 0) *
          𝒮 (1 + j) (osConcatIdx 1 j β (fun i => α (Fin.natAdd 1 i)))
            (osConcatPoint 1 j (osSplitOneLeft j x) (osSplitOneRight j x)))) =
      (if (fun _ : Fin 1 => α (Fin.castAdd j 0)) = β then 1 else 0) *
        𝒮 (1 + j) (osConcatIdx 1 j β (fun i => α (Fin.natAdd 1 i)))
          (osConcatPoint 1 j (osSplitOneLeft j x) (osSplitOneRight j x)) := by
    intro β
    have h_assoc : ∀ c : ι,
        star (S.C (α (Fin.castAdd j 0)) c) *
          (S.C c (β 0) *
            𝒮 (1 + j) (osConcatIdx 1 j β (fun i => α (Fin.natAdd 1 i)))
              (osConcatPoint 1 j (osSplitOneLeft j x) (osSplitOneRight j x))) =
        (star (S.C (α (Fin.castAdd j 0)) c) * S.C c (β 0)) *
          𝒮 (1 + j) (osConcatIdx 1 j β (fun i => α (Fin.natAdd 1 i)))
            (osConcatPoint 1 j (osSplitOneLeft j x) (osSplitOneRight j x)) :=
      fun _ => (mul_assoc _ _ _).symm
    simp_rw [h_assoc, ← Finset.sum_mul]
    congr 1
    have h_unit := sum_prod_star_C_mul_C S 1 (fun _ : Fin 1 => α (Fin.castAdd j 0)) β
    simp only [Fin.prod_univ_one] at h_unit
    rw [← h_unit]
    exact (Fintype.sum_equiv (Equiv.funUnique (Fin 1) ι)
      (fun γ : Fin 1 → ι => star (S.C (α (Fin.castAdd j 0)) (γ 0)) * S.C (γ 0) (β 0))
      (fun c : ι => star (S.C (α (Fin.castAdd j 0)) c) * S.C c (β 0))
      (fun _ => rfl)).symm
  simp_rw [h_collapse, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _), osConcatIdx_one_left,
      osConcatPoint_osSplitOne]
  exact (htrans (1 + j) α x hx (euclidTimeVec (osSplitOneTimeShift j x))).symm

theorem schwinger_one_add_eq_sum_inner_osBasisPre
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (htrans : OSTranslationInvariant D.𝒮)
    (j : ℕ) (α : Fin (1 + j) → ι) {x : Fin (1 + j) → Fin 4 → ℝ}
    (hx : x ∈ orderedEuclidN (1 + j)) :
    D.𝒮 (1 + j) α x =
      ∑ c : ι, star (S.C (α (Fin.castAdd j 0)) c) *
        ⟪osBasisPre D (osSplitOneLeftConfig j c x hx),
          osBasisPre D (osSplitOneRightConfig j α x hx)⟫_ℂ := by
  simp_rw [inner_osBasisPre]
  exact schwinger_one_add_eq_sum_osKernel S D.𝒮 htrans j α hx

theorem schwinger_one_add_eq_sum_inner_osBasis
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (htrans : OSTranslationInvariant D.𝒮)
    (j : ℕ) (α : Fin (1 + j) → ι) {x : Fin (1 + j) → Fin 4 → ℝ}
    (hx : x ∈ orderedEuclidN (1 + j)) :
    D.𝒮 (1 + j) α x =
      ∑ c : ι, star (S.C (α (Fin.castAdd j 0)) c) *
        ⟪osBasis D (osSplitOneLeftConfig j c x hx),
          osBasis D (osSplitOneRightConfig j α x hx)⟫_ℂ := by
  simp_rw [inner_osBasis]
  exact schwinger_one_add_eq_sum_osKernel S D.𝒮 htrans j α hx

lemma norm_osBasisPre_eq_zero_of_osKernel_self_eq_zero
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) {A : OSConfig ι}
    (hA : osKernel S D.𝒮 A A = 0) :
    ‖osBasisPre D A‖ = 0 := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), inner_osBasisPre, hA]
  simp

lemma inner_osBasisPre_eq_zero_of_osKernel_self_eq_zero
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) {A : OSConfig ι}
    (hA : osKernel S D.𝒮 A A = 0) (Φ : OSPreHilbertSpace D) :
    ⟪osBasisPre D A, Φ⟫_ℂ = 0 := by
  have h_cs := osPreHilbert_cauchy_schwarz D (osBasisPre D A) Φ
  rw [norm_osBasisPre_eq_zero_of_osKernel_self_eq_zero D hA, zero_mul] at h_cs
  exact norm_le_zero_iff.mp h_cs

theorem osBasis_eq_zero_of_osKernel_self_eq_zero
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) {A : OSConfig ι}
    (hA : osKernel S D.𝒮 A A = 0) :
    osBasis D A = 0 := by
  rw [← norm_eq_zero]
  dsimp [osBasis]
  rw [norm_toOSHilbert]
  exact norm_osBasisPre_eq_zero_of_osKernel_self_eq_zero D hA

theorem schwinger_one_add_eq_zero_of_component_onePoint_osKernel_eq_zero
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (htrans : OSTranslationInvariant D.𝒮)
    (α₀ : ι)
    (h1 : ∀ (c : ι) (y : posOrderedEuclidN 1),
      S.C α₀ c ≠ 0 → osKernel S D.𝒮 ⟨1, (fun _ => c, y)⟩ ⟨1, (fun _ => c, y)⟩ = 0)
    (j : ℕ) (α : Fin (1 + j) → ι) (hα₀ : α (Fin.castAdd j 0) = α₀)
    {x : Fin (1 + j) → Fin 4 → ℝ} (hx : x ∈ orderedEuclidN (1 + j)) :
    D.𝒮 (1 + j) α x = 0 := by
  rw [schwinger_one_add_eq_sum_inner_osBasisPre D htrans j α hx]
  refine Finset.sum_eq_zero (fun c _ => ?_)
  by_cases hc : S.C α₀ c = 0
  · rw [hα₀, hc, star_zero, zero_mul]
  · have h_zero : ⟪osBasisPre D (osSplitOneLeftConfig j c x hx),
        osBasisPre D (osSplitOneRightConfig j α x hx)⟫_ℂ = 0 :=
      inner_osBasisPre_eq_zero_of_osKernel_self_eq_zero D
        (h1 c ⟨osSplitOneLeft j x, osSplitOneLeft_mem_posOrderedEuclidN j hx⟩ hc)
        (osBasisPre D (osSplitOneRightConfig j α x hx))
    rw [h_zero, mul_zero]

theorem schwinger_eq_zero_of_onePoint_osKernel_eq_zero
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (htrans : OSTranslationInvariant D.𝒮)
    (h1 : ∀ (c : ι) (y : posOrderedEuclidN 1),
      osKernel S D.𝒮 ⟨1, (fun _ => c, y)⟩ ⟨1, (fun _ => c, y)⟩ = 0)
    (n : ℕ) (hn : 1 ≤ n) (α : Fin n → ι) {x : Fin n → Fin 4 → ℝ}
    (hx : x ∈ orderedEuclidN n) :
    D.𝒮 n α x = 0 := by
  have hn_eq : 1 + (n - 1) = n := Nat.add_sub_of_le hn
  rw [← schwinger_congr_n D.𝒮 hn_eq α x]
  have hx' : x ∘ finCongr hn_eq ∈ orderedEuclidN (1 + (n - 1)) := by
    intro i hi
    have hi' : (finCongr hn_eq i).val + 1 < n := by
      dsimp [finCongr]
      omega
    exact hx (finCongr hn_eq i) hi'
  exact schwinger_one_add_eq_zero_of_component_onePoint_osKernel_eq_zero D htrans
    ((α ∘ finCongr hn_eq) (Fin.castAdd (n - 1) 0))
    (fun c y _ => h1 c y) (n - 1) (α ∘ finCongr hn_eq) rfl hx'

lemma osKernel_eq_zero_of_schwinger_eq_zero
    {R : HolomorphicLorentzRep ι} (S : StarStructure R) (𝒮 : SchwingerFamily ι)
    (A B : OSConfig ι)
    (hS : ∀ (γ : Fin (A.1 + B.1) → ι) (z : Fin (A.1 + B.1) → Fin 4 → ℝ),
      z ∈ orderedEuclidN (A.1 + B.1) → 𝒮 (A.1 + B.1) γ z = 0) :
    osKernel S 𝒮 A B = 0 := by
  unfold osKernel
  refine Finset.sum_eq_zero (fun β _ => ?_)
  rw [hS _ _ (osConcatPoint_mem_orderedEuclidN A.1 B.1 A.2.2.property B.2.2.property), mul_zero]

theorem schwinger_eq_zero_of_twoPoint_eq_zero
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (htrans : OSTranslationInvariant D.𝒮)
    (h2 : ∀ (β : Fin 2 → ι) (y : Fin 2 → Fin 4 → ℝ),
      y ∈ orderedEuclidN 2 → D.𝒮 2 β y = 0)
    (n : ℕ) (hn : 1 ≤ n) (α : Fin n → ι) {x : Fin n → Fin 4 → ℝ}
    (hx : x ∈ orderedEuclidN n) :
    D.𝒮 n α x = 0 := by
  refine schwinger_eq_zero_of_onePoint_osKernel_eq_zero D htrans (fun c y => ?_) n hn α hx
  exact osKernel_eq_zero_of_schwinger_eq_zero S D.𝒮 ⟨1, (fun _ => c, y)⟩ ⟨1, (fun _ => c, y)⟩ h2

theorem schwinger_all_nPoint_eq_zero_iff_twoPoint_posOrdered_eq_zero
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (htrans : OSTranslationInvariant D.𝒮) :
    (∀ (n : ℕ), 1 ≤ n → ∀ (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → D.𝒮 n α x = 0) ↔
    (∀ (β : Fin 2 → ι) (y : Fin 2 → Fin 4 → ℝ),
      y ∈ posOrderedEuclidN 2 → D.𝒮 2 β y = 0) := by
  constructor
  · intro hall β y hy
    exact hall 2 (by omega) β y (posOrderedEuclidN_subset_orderedEuclidN 2 hy)
  · intro h2_pos n hn α x hx
    refine schwinger_eq_zero_of_twoPoint_eq_zero D htrans (fun β y hy => ?_) n hn α hx
    exact schwinger_eq_zero_of_posOrderedEuclidN_eq_zero htrans 2 β (h2_pos β) hy

theorem osKernel_eq_zero_of_twoPoint_eq_zero
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (htrans : OSTranslationInvariant D.𝒮)
    (h2 : ∀ (β : Fin 2 → ι) (y : Fin 2 → Fin 4 → ℝ),
      y ∈ orderedEuclidN 2 → D.𝒮 2 β y = 0)
    (A B : OSConfig ι) (hAB : 1 ≤ A.1 + B.1) :
    osKernel S D.𝒮 A B = 0 :=
  osKernel_eq_zero_of_schwinger_eq_zero S D.𝒮 A B
    (fun γ _z hz => schwinger_eq_zero_of_twoPoint_eq_zero D htrans h2 (A.1 + B.1) hAB γ hz)

theorem osBasis_eq_zero_of_twoPoint_eq_zero
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (htrans : OSTranslationInvariant D.𝒮)
    (h2 : ∀ (β : Fin 2 → ι) (y : Fin 2 → Fin 4 → ℝ),
      y ∈ orderedEuclidN 2 → D.𝒮 2 β y = 0)
    (A : OSConfig ι) (hA : 1 ≤ A.1) :
    osBasis D A = 0 :=
  osBasis_eq_zero_of_osKernel_self_eq_zero D
    (osKernel_eq_zero_of_twoPoint_eq_zero D htrans h2 A A (by omega))

omit [Fintype ι] [DecidableEq ι] in
lemma osConfig_eq_osVacuumConfig_of_fst_eq_zero {A : OSConfig ι} (hA : A.1 = 0) :
    A = osVacuumConfig ι := by
  rcases A with ⟨n, α, x, hx⟩
  dsimp at hA
  subst hA
  unfold osVacuumConfig
  congr 1
  ext i
  · exact Fin.elim0 i
  · exact Fin.elim0 i

theorem toOSHilbert_eq_coeff_smul_osVacuum_of_twoPoint_eq_zero
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (htrans : OSTranslationInvariant D.𝒮)
    (h2 : ∀ (β : Fin 2 → ι) (y : Fin 2 → Fin 4 → ℝ),
      y ∈ orderedEuclidN 2 → D.𝒮 2 β y = 0)
    (Ψ : OSPreHilbertSpace D) :
    toOSHilbert D Ψ = (Ψ.toFinsupp (osVacuumConfig ι)) • osVacuum D := by
  classical
  conv_lhs => rw [osPreHilbert_eq_finsupp_sum_osBasisPre D Ψ]
  rw [map_finsuppSum]
  unfold Finsupp.sum
  have h_term : ∀ A ∈ Ψ.toFinsupp.support,
      toOSHilbert D (Ψ.toFinsupp A • osBasisPre D A) =
        if A = osVacuumConfig ι then (Ψ.toFinsupp (osVacuumConfig ι)) • osVacuum D else 0 := by
    intro A _
    rw [(toOSHilbert D).map_smul]
    change Ψ.toFinsupp A • osBasis D A = _
    by_cases hA : A = osVacuumConfig ι
    · subst hA
      rw [if_pos rfl]
      rfl
    · rw [if_neg hA]
      have hA_pos : 1 ≤ A.1 := by
        by_contra hc
        have h0 : A.1 = 0 := by omega
        exact hA (osConfig_eq_osVacuumConfig_of_fst_eq_zero h0)
      rw [osBasis_eq_zero_of_twoPoint_eq_zero D htrans h2 A hA_pos, smul_zero]
  rw [Finset.sum_congr rfl h_term, Finset.sum_ite_eq']
  split_ifs with hmem
  · rfl
  · rw [Finsupp.notMem_support_iff.mp hmem, zero_smul]

theorem eq_smul_osVacuum_of_twoPoint_eq_zero
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (htrans : OSTranslationInvariant D.𝒮)
    (hnorm : OSVacuumNormalized D.𝒮)
    (h2 : ∀ (β : Fin 2 → ι) (y : Fin 2 → Fin 4 → ℝ),
      y ∈ orderedEuclidN 2 → D.𝒮 2 β y = 0)
    (Φ : OSHilbert D) :
    Φ = ⟪osVacuum D, Φ⟫_ℂ • osVacuum D := by
  induction Φ using UniformSpace.Completion.induction_on with
  | hp =>
    exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih Ψ =>
    change toOSHilbert D Ψ = ⟪osVacuum D, toOSHilbert D Ψ⟫_ℂ • osVacuum D
    have hΨ := toOSHilbert_eq_coeff_smul_osVacuum_of_twoPoint_eq_zero D htrans h2 Ψ
    rw [hΨ, inner_smul_right, inner_osVacuum_self_of_normalized D hnorm, mul_one]

namespace OSReconstructedWightman

variable {R : HolomorphicLorentzRep ι} {S : StarStructure R}
  {η : ℂ} {𝒮 : SchwingerFamily ι}

theorem schwinger_eq_zero_of_twoPoint_eq_zero
    (P : OSReconstructedWightman R S η 𝒮)
    (h2 : ∀ (β : Fin 2 → ι) (y : Fin 2 → Fin 4 → ℝ),
      y ∈ orderedEuclidN 2 → 𝒮 2 β y = 0)
    (n : ℕ) (hn : 1 ≤ n) (α : Fin n → ι) {x : Fin n → Fin 4 → ℝ}
    (hx : x ∈ orderedEuclidN n) :
    𝒮 n α x = 0 :=
  _root_.QFT.schwinger_eq_zero_of_twoPoint_eq_zero P.osData P.osAxioms.os1_translation
    h2 n hn α hx

theorem tube_eq_zero_of_twoPoint_eq_zero
    (P : OSReconstructedWightman R S η 𝒮)
    (h2 : ∀ (β : Fin 2 → ι) (y : Fin 2 → Fin 4 → ℝ),
      y ∈ orderedEuclidN 2 → 𝒮 2 β y = 0)
    (n : ℕ) (hn : 1 ≤ n) (α : Fin n → ι) :
    ∀ w ∈ forward_tube_n n, P.E.H n α w = 0 := by
  intro w hw
  refine analyticOn_forward_tube_eq_zero_of_posOrderedEuclidN_eq_zero n
    (P.E.analytic n α) (fun x hx => ?_) w hw
  have hx' := posOrderedEuclidN_subset_orderedEuclidN n hx
  change schwingerFromTube P.E n α x = 0
  rw [← P.schwinger_eq n α x hx']
  exact P.schwinger_eq_zero_of_twoPoint_eq_zero h2 n hn α hx'

theorem wightman_eq_zero_of_twoPoint_eq_zero
    (P : OSReconstructedWightman R S η 𝒮)
    (h2 : ∀ (β : Fin 2 → ι) (y : Fin 2 → Fin 4 → ℝ),
      y ∈ orderedEuclidN 2 → 𝒮 2 β y = 0)
    (n : ℕ) (hn : 1 ≤ n) (α : Fin n → ι)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    P.W n α f = 0 :=
  wightman_eq_zero_of_tube_eq_zero P.E n α
    (fun w hw => P.tube_eq_zero_of_twoPoint_eq_zero h2 n hn α w hw) f

theorem wrong_statistics_all_nPoint_eq_zero
    (P : OSReconstructedWightman R S η 𝒮)
    {ε : ℂ} (hε : R.HasSpinParity ε) (h_exch : TwoPointSpinExchange ε P.E)
    (h_wrong : η ≠ ε) :
    (∀ (n : ℕ), 1 ≤ n → ∀ (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → 𝒮 n α x = 0) ∧
    (∀ (n : ℕ), 1 ≤ n → ∀ (α : Fin n → ι) (z : Fin n → Fin 4 → ℂ),
      z ∈ forward_tube_n n → P.E.H n α z = 0) ∧
    (∀ (n : ℕ), 1 ≤ n → ∀ (α : Fin n → ι) (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ),
      P.W n α f = 0) ∧
    (OSVacuumNormalized 𝒮 → ∀ Φ : P.Hilbert, Φ = ⟪P.vacuum, Φ⟫_ℂ • P.vacuum) := by
  have h2 : ∀ (β : Fin 2 → ι) (y : Fin 2 → Fin 4 → ℝ),
      y ∈ orderedEuclidN 2 → 𝒮 2 β y = 0 := by
    intro β y hy
    by_contra hne
    have h_rev : (β ∘ Fin.rev) ∘ Fin.rev = β := by
      ext i
      simp [Fin.rev_rev]
    refine h_wrong (P.spin_statistics_from_schwinger hε h_exch ⟨β ∘ Fin.rev, y, hy, ?_⟩)
    rwa [h_rev]
  refine ⟨fun n hn α x hx => P.schwinger_eq_zero_of_twoPoint_eq_zero h2 n hn α hx,
    fun n hn α z hz => P.tube_eq_zero_of_twoPoint_eq_zero h2 n hn α z hz,
    fun n hn α f => P.wightman_eq_zero_of_twoPoint_eq_zero h2 n hn α f,
    fun hnorm Φ => eq_smul_osVacuum_of_twoPoint_eq_zero P.osData P.osAxioms.os1_translation
      hnorm h2 Φ⟩

theorem spin_statistics_of_any_schwinger_ne_zero
    (P : OSReconstructedWightman R S η 𝒮)
    {ε : ℂ} (hε : R.HasSpinParity ε) (h_exch : TwoPointSpinExchange ε P.E)
    (h_nondeg : ∃ (n : ℕ) (_ : 1 ≤ n) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n ∧ 𝒮 n α x ≠ 0) :
    η = ε := by
  by_contra h_wrong
  rcases h_nondeg with ⟨n, hn, α, x, hx, hne⟩
  exact hne ((P.wrong_statistics_all_nPoint_eq_zero hε h_exch h_wrong).1 n hn α x hx)

theorem spin_statistics_of_any_wightman_ne_zero
    (P : OSReconstructedWightman R S η 𝒮)
    {ε : ℂ} (hε : R.HasSpinParity ε) (h_exch : TwoPointSpinExchange ε P.E)
    (h_nondeg : ∃ (n : ℕ) (_ : 1 ≤ n) (α : Fin n → ι)
      (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ), P.W n α f ≠ 0) :
    η = ε := by
  by_contra h_wrong
  rcases h_nondeg with ⟨n, hn, α, f, hf⟩
  exact hf ((P.wrong_statistics_all_nPoint_eq_zero hε h_exch h_wrong).2.2.1 n hn α f)

theorem spin_statistics_of_subsingleton_any_wightman_ne_zero [Subsingleton ι]
    (P : OSReconstructedWightman R S η 𝒮) (hε : R.HasSpinParity 1)
    (h_nondeg : ∃ (n : ℕ) (_ : 1 ≤ n) (α : Fin n → ι)
      (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ), P.W n α f ≠ 0) :
    η = 1 :=
  P.spin_statistics_of_any_wightman_ne_zero hε P.twoPointSpinExchange_of_subsingleton_index h_nondeg

theorem subsingleton_fermion_all_nPoint_eq_zero [Subsingleton ι]
    (P : OSReconstructedWightman R S (-1) 𝒮) :
    (∀ (n : ℕ), 1 ≤ n → ∀ (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → 𝒮 n α x = 0) ∧
    (∀ (n : ℕ), 1 ≤ n → ∀ (α : Fin n → ι) (z : Fin n → Fin 4 → ℂ),
      z ∈ forward_tube_n n → P.E.H n α z = 0) ∧
    (∀ (n : ℕ), 1 ≤ n → ∀ (α : Fin n → ι) (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ),
      P.W n α f = 0) ∧
    (OSVacuumNormalized 𝒮 → ∀ Φ : P.Hilbert, Φ = ⟪P.vacuum, Φ⟫_ℂ • P.vacuum) := by
  have h2 : ∀ (β : Fin 2 → ι) (y : Fin 2 → Fin 4 → ℝ),
      y ∈ orderedEuclidN 2 → 𝒮 2 β y = 0 := by
    intro β y hy
    have hβ : β = fun _ => β 0 := by
      ext i
      exact Subsingleton.elim _ _
    rw [hβ, P.schwinger_eq 2 (fun _ => β 0) y hy]
    exact P.fermion_tube_twoPoint_diag_eq_zero (β 0) (wickEmbedN 2 y)
      (wickEmbedN_mem_forward_tube_n 2 hy)
  refine ⟨fun n hn α x hx => P.schwinger_eq_zero_of_twoPoint_eq_zero h2 n hn α hx,
    fun n hn α z hz => P.tube_eq_zero_of_twoPoint_eq_zero h2 n hn α z hz,
    fun n hn α f => P.wightman_eq_zero_of_twoPoint_eq_zero h2 n hn α f,
    fun hnorm Φ => eq_smul_osVacuum_of_twoPoint_eq_zero P.osData P.osAxioms.os1_translation
      hnorm h2 Φ⟩

theorem spin_statistics_of_euclidIndexExchange_any_wightman_ne_zero
    (P : OSReconstructedWightman R S η 𝒮)
    {ε : ℂ} (hε : R.HasSpinParity ε)
    (heuclid : EuclidTwoPointIndexExchange ε 𝒮)
    (h_nondeg : ∃ (n : ℕ) (_ : 1 ≤ n) (α : Fin n → ι)
      (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ), P.W n α f ≠ 0) :
    η = ε :=
  P.spin_statistics_of_any_wightman_ne_zero hε (P.twoPointSpinExchange_of_euclid heuclid) h_nondeg

end OSReconstructedWightman

theorem scalar_os_spin_statistics_any_nPoint {η : ℂ} {𝒮 : SchwingerFamily Unit}
    (P : ScalarOSReconstructedWightman η 𝒮)
    (h_nondeg : ∃ (n : ℕ) (_ : 1 ≤ n) (α : Fin n → Unit)
      (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ), P.W n α f ≠ 0) :
    η = 1 :=
  P.spin_statistics_of_subsingleton_any_wightman_ne_zero trivialRep_spinParity h_nondeg

theorem vector_os_spin_statistics_any_nPoint {η : ℂ} {𝒮 : SchwingerFamily (Fin 4)}
    (P : VectorOSReconstructedWightman η 𝒮)
    (heuclid : EuclidTwoPointIndexExchange 1 𝒮)
    (h_nondeg : ∃ (n : ℕ) (_ : 1 ≤ n) (α : Fin n → Fin 4)
      (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ), P.W n α f ≠ 0) :
    η = 1 :=
  P.spin_statistics_of_euclidIndexExchange_any_wightman_ne_zero stdRep_spinParity heuclid h_nondeg

theorem dirac_os_spin_statistics_any_nPoint {η : ℂ} {𝒮 : SchwingerFamily (Fin 2 ⊕ Fin 2)}
    (P : DiracOSReconstructedWightman η 𝒮)
    (heuclid : EuclidTwoPointIndexExchange (-1) 𝒮)
    (h_nondeg : ∃ (n : ℕ) (_ : 1 ≤ n) (α : Fin n → Fin 2 ⊕ Fin 2)
      (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ), P.W n α f ≠ 0) :
    η = -1 :=
  P.spin_statistics_of_euclidIndexExchange_any_wightman_ne_zero
    diracRep_spinParity heuclid h_nondeg

theorem spinorTensorBispinor_os_spin_statistics_any_nPoint
    (m₁ m₂ : ℕ) {η : ℂ}
    {𝒮 : SchwingerFamily (((Fin m₁ → Fin 2) × (Fin m₂ → Fin 2)) ⊕
      ((Fin m₁ → Fin 2) × (Fin m₂ → Fin 2)))}
    (P : SpinorTensorBispinorOSReconstructedWightman m₁ m₂ η 𝒮)
    (heuclid : EuclidTwoPointIndexExchange ((-1 : ℂ) ^ (m₁ + m₂)) 𝒮)
    (h_nondeg : ∃ (n : ℕ) (_ : 1 ≤ n)
      (α : Fin n → ((Fin m₁ → Fin 2) × (Fin m₂ → Fin 2)) ⊕
        ((Fin m₁ → Fin 2) × (Fin m₂ → Fin 2)))
      (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ), P.W n α f ≠ 0) :
    η = (-1 : ℂ) ^ (m₁ + m₂) :=
  P.spin_statistics_of_euclidIndexExchange_any_wightman_ne_zero
    (directSumRep_spinParity (spinorTensorRep_spinParity m₁ m₂)
      (chiralSwapRep_spinParity (spinorTensorRep_spinParity m₁ m₂)))
    heuclid h_nondeg

omit [Fintype ι] [DecidableEq ι] in
def TubeBoundaryInjective {W : WightmanFamily ι} (E : TubeExtension W) : Prop :=
  ∀ (n : ℕ) (α : Fin n → ι),
    (∀ f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ, W n α f = 0) →
    ∀ z ∈ forward_tube_n n, E.H n α z = 0

omit [Fintype ι] [DecidableEq ι] in
theorem vladimirov_H_eq_zero_of_wightman_eq_zero {W : WightmanFamily ι}
    (n : ℕ) (α : Fin n → ι)
    (hW : ∀ f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ, W n α f = 0)
    (z : Fin n → Fin 4 → ℂ) :
    vladimirov_H W n α z = 0 :=
  hW (invMinkowskiFourierCLM n (vladimirov_psi_schwartz n 1 Real.zero_lt_one z))

theorem vladimirov_tubeBoundaryInjective (R : HolomorphicLorentzRep ι)
    (W : WightmanFamily ι) (hspec : SpectrumCondition W) (hP : PoincareCovariant R W) :
    TubeBoundaryInjective (vladimirovTubeExtension R W hspec hP) :=
  fun n α hW z _ => vladimirov_H_eq_zero_of_wightman_eq_zero n α hW z

omit [Fintype ι] [DecidableEq ι] in
theorem wightman_eq_zero_iff_tube_eq_zero {W : WightmanFamily ι}
    (E : TubeExtension W) (hinj : TubeBoundaryInjective E)
    (n : ℕ) (α : Fin n → ι) :
    (∀ f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ, W n α f = 0) ↔
      (∀ z ∈ forward_tube_n n, E.H n α z = 0) :=
  ⟨hinj n α, fun hH f => wightman_eq_zero_of_tube_eq_zero E n α hH f⟩

omit [Fintype ι] [DecidableEq ι] in
theorem schwingerFromTube_eq_zero_of_wightman_eq_zero {W : WightmanFamily ι}
    (E : TubeExtension W) (hinj : TubeBoundaryInjective E)
    (n : ℕ) (α : Fin n → ι)
    (hW : ∀ f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ, W n α f = 0)
    {x : Fin n → Fin 4 → ℝ} (hx : x ∈ orderedEuclidN n) :
    schwingerFromTube E n α x = 0 :=
  hinj n α hW (wickEmbedN n x) (wickEmbedN_mem_forward_tube_n n hx)

namespace OSReconstructedWightman

variable {R : HolomorphicLorentzRep ι} {S : StarStructure R}
  {η : ℂ} {𝒮 : SchwingerFamily ι}

theorem all_nPoint_eq_zero_of_wightman_twoPoint_eq_zero
    (P : OSReconstructedWightman R S η 𝒮) (hinj : TubeBoundaryInjective P.E)
    (hW2 : ∀ (β : Fin 2 → ι) (f : SchwartzMap (Fin 2 → Fin 4 → ℝ) ℂ), P.W 2 β f = 0) :
    (∀ (n : ℕ), 1 ≤ n → ∀ (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → 𝒮 n α x = 0) ∧
    (∀ (n : ℕ), 1 ≤ n → ∀ (α : Fin n → ι) (z : Fin n → Fin 4 → ℂ),
      z ∈ forward_tube_n n → P.E.H n α z = 0) ∧
    (∀ (n : ℕ), 1 ≤ n → ∀ (α : Fin n → ι) (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ),
      P.W n α f = 0) ∧
    (OSVacuumNormalized 𝒮 → ∀ Φ : P.Hilbert, Φ = ⟪P.vacuum, Φ⟫_ℂ • P.vacuum) := by
  have h2 : ∀ (β : Fin 2 → ι) (y : Fin 2 → Fin 4 → ℝ),
      y ∈ orderedEuclidN 2 → 𝒮 2 β y = 0 := by
    intro β y hy
    rw [P.schwinger_eq 2 β y hy]
    exact schwingerFromTube_eq_zero_of_wightman_eq_zero P.E hinj 2 β (hW2 β) hy
  refine ⟨fun n hn α x hx => P.schwinger_eq_zero_of_twoPoint_eq_zero h2 n hn α hx,
    fun n hn α z hz => P.tube_eq_zero_of_twoPoint_eq_zero h2 n hn α z hz,
    fun n hn α f => P.wightman_eq_zero_of_twoPoint_eq_zero h2 n hn α f,
    fun hnorm Φ => eq_smul_osVacuum_of_twoPoint_eq_zero P.osData P.osAxioms.os1_translation
      hnorm h2 Φ⟩

theorem wightman_all_nPoint_eq_zero_iff_wightman_twoPoint_eq_zero
    (P : OSReconstructedWightman R S η 𝒮) (hinj : TubeBoundaryInjective P.E) :
    (∀ (n : ℕ), 1 ≤ n → ∀ (α : Fin n → ι) (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ),
      P.W n α f = 0) ↔
    (∀ (β : Fin 2 → ι) (f : SchwartzMap (Fin 2 → Fin 4 → ℝ) ℂ), P.W 2 β f = 0) :=
  ⟨fun hall β f => hall 2 (by omega) β f,
   fun hW2 => (P.all_nPoint_eq_zero_of_wightman_twoPoint_eq_zero hinj hW2).2.2.1⟩

end OSReconstructedWightman

theorem vladimirovOSReconstruction_wightman_all_nPoint_eq_zero_iff_twoPoint_eq_zero
    (R : HolomorphicLorentzRep ι) (S : StarStructure R)
    (W : WightmanFamily ι) {η : ℂ}
    (hspec : SpectrumCondition W) (hP : PoincareCovariant R W)
    (hloc : WeakLocality η W) (hpos : Positivity S W)
    (hherm : TubeWickHermiticity S (vladimirovTubeExtension R W hspec hP))
    (hrp : OSReflectionPositive S (vladimirovSchwinger W))
    (hcontr : OSContractionCondition
      { 𝒮 := vladimirovSchwinger W
        hermiticity := schwingerFromTube_os_hermiticity S _ hherm
        positivity := hrp })
    (ℰ : OSHolomorphicSemigroup
      { 𝒮 := vladimirovSchwinger W
        hermiticity := schwingerFromTube_os_hermiticity S _ hherm
        positivity := hrp }
      hcontr) :
    (∀ (n : ℕ), 1 ≤ n → ∀ (α : Fin n → ι) (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ),
      W n α f = 0) ↔
    (∀ (β : Fin 2 → ι) (f : SchwartzMap (Fin 2 → Fin 4 → ℝ) ℂ), W 2 β f = 0) :=
  (vladimirovOSReconstruction R S W hspec hP hloc hpos hherm hrp hcontr ℰ)
    |>.wightman_all_nPoint_eq_zero_iff_wightman_twoPoint_eq_zero
      (vladimirov_tubeBoundaryInjective R W hspec hP)

def DiagonalStarStructure {R : HolomorphicLorentzRep ι} (S : StarStructure R) : Prop :=
  ∀ a b : ι, a ≠ b → S.C a b = 0

lemma diagonalStarStructure_of_C_eq_one {R : HolomorphicLorentzRep ι}
    (S : StarStructure R) (hC : S.C = 1) :
    DiagonalStarStructure S := by
  intro a b hab
  rw [hC, Matrix.one_apply_ne hab]

lemma diagonalStarStructure_trivialStarStructure :
    DiagonalStarStructure trivialStarStructure :=
  diagonalStarStructure_of_C_eq_one trivialStarStructure rfl

lemma diagonalStarStructure_stdStarStructure :
    DiagonalStarStructure stdStarStructure :=
  diagonalStarStructure_of_C_eq_one stdStarStructure rfl

lemma diagonalStarStructure_directSum {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁]
    [Fintype ι₂] [DecidableEq ι₂]
    {R₁ : HolomorphicLorentzRep ι₁} {R₂ : HolomorphicLorentzRep ι₂}
    {S₁ : StarStructure R₁} {S₂ : StarStructure R₂}
    (h₁ : DiagonalStarStructure S₁) (h₂ : DiagonalStarStructure S₂) :
    DiagonalStarStructure (directSumStarStructure S₁ S₂) := by
  rintro (a₁ | a₂) (b₁ | b₂) hab
  · exact h₁ a₁ b₁ (fun h => hab (congrArg Sum.inl h))
  · rfl
  · rfl
  · exact h₂ a₂ b₂ (fun h => hab (congrArg Sum.inr h))

lemma diagonalStarStructure_tensorProd {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁]
    [Fintype ι₂] [DecidableEq ι₂]
    {R₁ : HolomorphicLorentzRep ι₁} {R₂ : HolomorphicLorentzRep ι₂}
    {S₁ : StarStructure R₁} {S₂ : StarStructure R₂}
    (h₁ : DiagonalStarStructure S₁) (h₂ : DiagonalStarStructure S₂) :
    DiagonalStarStructure (tensorProdStarStructure S₁ S₂) := by
  rintro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ hab
  change S₁.C a₁ b₁ * S₂.C a₂ b₂ = 0
  by_cases h : a₁ = b₁
  · have h' : a₂ ≠ b₂ := fun h2 => hab (Prod.ext h h2)
    rw [h₂ a₂ b₂ h', mul_zero]
  · rw [h₁ a₁ b₁ h, zero_mul]

lemma diagonalStarStructure_mul_star_self {R : HolomorphicLorentzRep ι}
    {S : StarStructure R} (hdiag : DiagonalStarStructure S) (c : ι) :
    S.C c c * star (S.C c c) = 1 := by
  have h := congrFun (congrFun S.involutive c) c
  simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.one_apply_eq] at h
  rw [← h]
  symm
  refine Finset.sum_eq_single c (fun b _ hbc => ?_) (fun hc => False.elim (hc (Finset.mem_univ c)))
  rw [hdiag c b (Ne.symm hbc), zero_mul]

lemma diagonalStarStructure_diag_ne_zero {R : HolomorphicLorentzRep ι}
    {S : StarStructure R} (hdiag : DiagonalStarStructure S) (c : ι) :
    S.C c c ≠ 0 := by
  intro hc
  have h := diagonalStarStructure_mul_star_self hdiag c
  rw [hc, zero_mul] at h
  exact zero_ne_one h

omit [Fintype ι] [DecidableEq ι] in
@[simp]
lemma osConcatIdx_one_one_const (c : ι) :
    osConcatIdx 1 1 (fun _ => c) (fun _ => c) = fun _ => c := by
  ext i
  dsimp [osConcatIdx]
  by_cases hi : i.val < 1
  · rw [fin_append_apply_lt _ _ i hi]
    rfl
  · rw [fin_append_apply_ge _ _ i (by omega)]

theorem osKernel_onePoint_self_of_diagonalStarStructure
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (hdiag : DiagonalStarStructure S) (𝒮 : SchwingerFamily ι)
    (c : ι) (y : posOrderedEuclidN 1) :
    osKernel S 𝒮 ⟨1, (fun _ => c, y)⟩ ⟨1, (fun _ => c, y)⟩ =
      S.C c c * 𝒮 2 (fun _ => c) (osConcatPoint 1 1 y.val y.val) := by
  unfold osKernel
  dsimp only
  refine (Finset.sum_eq_single (fun _ : Fin 1 => c) (fun β _ hβ => ?_)
    (fun hc => False.elim (hc (Finset.mem_univ _)))).trans ?_
  · have hβ0 : β 0 ≠ c := by
      intro h0
      apply hβ
      ext i
      fin_cases i
      exact h0
    rw [Fin.prod_univ_one, hdiag c (β 0) (Ne.symm hβ0), zero_mul]
  · rw [Fin.prod_univ_one, osConcatIdx_one_one_const]

theorem schwinger_one_add_eq_zero_of_diag_twoPoint_component_eq_zero
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (htrans : OSTranslationInvariant D.𝒮)
    (hdiag : DiagonalStarStructure S) (c : ι)
    (hc2 : ∀ y ∈ orderedEuclidN 2, D.𝒮 2 (fun _ => c) y = 0)
    (j : ℕ) (α : Fin (1 + j) → ι) (hα₀ : α (Fin.castAdd j 0) = c)
    {x : Fin (1 + j) → Fin 4 → ℝ} (hx : x ∈ orderedEuclidN (1 + j)) :
    D.𝒮 (1 + j) α x = 0 := by
  refine schwinger_one_add_eq_zero_of_component_onePoint_osKernel_eq_zero D htrans c
    (fun b y hcb => ?_) j α hα₀ hx
  have hbc : c = b := by
    by_contra hne
    exact hcb (hdiag c b hne)
  subst hbc
  rw [osKernel_onePoint_self_of_diagonalStarStructure hdiag D.𝒮 c y,
      hc2 _ (osConcatPoint_mem_orderedEuclidN 1 1 y.property y.property), mul_zero]

theorem schwinger_eq_zero_of_diag_twoPoint_eq_zero
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (htrans : OSTranslationInvariant D.𝒮)
    (hdiag : DiagonalStarStructure S)
    (h2_diag : ∀ (c : ι) (y : Fin 2 → Fin 4 → ℝ),
      y ∈ orderedEuclidN 2 → D.𝒮 2 (fun _ => c) y = 0)
    (n : ℕ) (hn : 1 ≤ n) (α : Fin n → ι) {x : Fin n → Fin 4 → ℝ}
    (hx : x ∈ orderedEuclidN n) :
    D.𝒮 n α x = 0 := by
  refine schwinger_eq_zero_of_onePoint_osKernel_eq_zero D htrans (fun c y => ?_) n hn α hx
  rw [osKernel_onePoint_self_of_diagonalStarStructure hdiag D.𝒮 c y,
      h2_diag c _ (osConcatPoint_mem_orderedEuclidN 1 1 y.property y.property), mul_zero]

theorem schwinger_all_nPoint_eq_zero_iff_diag_twoPoint_posOrdered_eq_zero
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (htrans : OSTranslationInvariant D.𝒮)
    (hdiag : DiagonalStarStructure S) :
    (∀ (n : ℕ), 1 ≤ n → ∀ (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → D.𝒮 n α x = 0) ↔
    (∀ (c : ι) (y : Fin 2 → Fin 4 → ℝ),
      y ∈ posOrderedEuclidN 2 → D.𝒮 2 (fun _ => c) y = 0) := by
  constructor
  · intro hall c y hy
    exact hall 2 (by omega) (fun _ => c) y (posOrderedEuclidN_subset_orderedEuclidN 2 hy)
  · intro h2_pos n hn α x hx
    refine schwinger_eq_zero_of_diag_twoPoint_eq_zero D htrans hdiag (fun c y hy => ?_) n hn α hx
    exact schwinger_eq_zero_of_posOrderedEuclidN_eq_zero htrans 2 (fun _ => c) (h2_pos c) hy

omit [Fintype ι] [DecidableEq ι] in
theorem tube_twoPoint_diag_eq_zero_of_eta_ne_one {W : WightmanFamily ι} {η : ℂ}
    (E : TubeExtension W) (htrans : TubeTranslationInvariant E)
    (hloc : TubeWeakLocality η E) (hη : η ≠ 1)
    (c : ι) (z : Fin 2 → Fin 4 → ℂ) (hz : z ∈ forward_tube_n 2) :
    E.H 2 (fun _ => c) z = 0 := by
  have h := tube_twoPoint_diag_eq_eta_mul E htrans hloc c z hz
  have h_sub : (1 - η) * E.H 2 (fun _ => c) z = 0 := by
    linear_combination h
  exact (mul_eq_zero.mp h_sub).resolve_left (sub_ne_zero.mpr hη.symm)

namespace OSReconstructedWightman

variable {R : HolomorphicLorentzRep ι} {S : StarStructure R}
  {η : ℂ} {𝒮 : SchwingerFamily ι}

theorem schwinger_twoPoint_diag_eq_zero_of_eta_ne_one
    (P : OSReconstructedWightman R S η 𝒮) (hη : η ≠ 1)
    (c : ι) {y : Fin 2 → Fin 4 → ℝ} (hy : y ∈ orderedEuclidN 2) :
    𝒮 2 (fun _ => c) y = 0 := by
  rw [P.schwinger_eq 2 (fun _ => c) y hy]
  exact tube_twoPoint_diag_eq_zero_of_eta_ne_one P.E P.tube_translationInvariant
    P.tube_weakLocality hη c (wickEmbedN 2 y) (wickEmbedN_mem_forward_tube_n 2 hy)

theorem all_nPoint_eq_zero_of_diagonalStarStructure_of_eta_ne_one
    (P : OSReconstructedWightman R S η 𝒮) (hdiag : DiagonalStarStructure S) (hη : η ≠ 1) :
    (∀ (n : ℕ), 1 ≤ n → ∀ (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → 𝒮 n α x = 0) ∧
    (∀ (n : ℕ), 1 ≤ n → ∀ (α : Fin n → ι) (z : Fin n → Fin 4 → ℂ),
      z ∈ forward_tube_n n → P.E.H n α z = 0) ∧
    (∀ (n : ℕ), 1 ≤ n → ∀ (α : Fin n → ι) (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ),
      P.W n α f = 0) ∧
    (OSVacuumNormalized 𝒮 → ∀ Φ : P.Hilbert, Φ = ⟪P.vacuum, Φ⟫_ℂ • P.vacuum) := by
  have h2 : ∀ (β : Fin 2 → ι) (y : Fin 2 → Fin 4 → ℝ),
      y ∈ orderedEuclidN 2 → 𝒮 2 β y = 0 :=
    fun β _y hy => schwinger_eq_zero_of_diag_twoPoint_eq_zero P.osData
      P.osAxioms.os1_translation hdiag
      (fun c _z hz => P.schwinger_twoPoint_diag_eq_zero_of_eta_ne_one hη c hz)
      2 (by omega) β hy
  refine ⟨fun n hn α x hx => P.schwinger_eq_zero_of_twoPoint_eq_zero h2 n hn α hx,
    fun n hn α z hz => P.tube_eq_zero_of_twoPoint_eq_zero h2 n hn α z hz,
    fun n hn α f => P.wightman_eq_zero_of_twoPoint_eq_zero h2 n hn α f,
    fun hnorm Φ => eq_smul_osVacuum_of_twoPoint_eq_zero P.osData P.osAxioms.os1_translation
      hnorm h2 Φ⟩

theorem spin_statistics_of_diagonalStarStructure_any_schwinger_ne_zero
    (P : OSReconstructedWightman R S η 𝒮) (hdiag : DiagonalStarStructure S)
    (h_nondeg : ∃ (n : ℕ) (_ : 1 ≤ n) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n ∧ 𝒮 n α x ≠ 0) :
    η = 1 := by
  by_contra hη
  rcases h_nondeg with ⟨n, hn, α, x, hx, hne⟩
  exact hne
    ((P.all_nPoint_eq_zero_of_diagonalStarStructure_of_eta_ne_one hdiag hη).1 n hn α x hx)

theorem spin_statistics_of_diagonalStarStructure_any_wightman_ne_zero
    (P : OSReconstructedWightman R S η 𝒮) (hdiag : DiagonalStarStructure S)
    (h_nondeg : ∃ (n : ℕ) (_ : 1 ≤ n) (α : Fin n → ι)
      (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ), P.W n α f ≠ 0) :
    η = 1 := by
  by_contra hη
  rcases h_nondeg with ⟨n, hn, α, f, hf⟩
  exact hf
    ((P.all_nPoint_eq_zero_of_diagonalStarStructure_of_eta_ne_one hdiag hη).2.2.1 n hn α f)

end OSReconstructedWightman

theorem vector_os_spin_statistics_unconditional {η : ℂ} {𝒮 : SchwingerFamily (Fin 4)}
    (P : VectorOSReconstructedWightman η 𝒮)
    (h_nondeg : ∃ (α : Fin 2 → Fin 4) (f : SchwartzMap (Fin 2 → Fin 4 → ℝ) ℂ), P.W 2 α f ≠ 0) :
    η = 1 := by
  rcases h_nondeg with ⟨α, f, hf⟩
  exact P.spin_statistics_of_diagonalStarStructure_any_wightman_ne_zero
    diagonalStarStructure_stdStarStructure ⟨2, by omega, α, f, hf⟩

theorem vector_os_spin_statistics_any_nPoint_unconditional {η : ℂ} {𝒮 : SchwingerFamily (Fin 4)}
    (P : VectorOSReconstructedWightman η 𝒮)
    (h_nondeg : ∃ (n : ℕ) (_ : 1 ≤ n) (α : Fin n → Fin 4)
      (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ), P.W n α f ≠ 0) :
    η = 1 :=
  P.spin_statistics_of_diagonalStarStructure_any_wightman_ne_zero
    diagonalStarStructure_stdStarStructure h_nondeg

theorem vector_os_fermion_all_nPoint_eq_zero {𝒮 : SchwingerFamily (Fin 4)}
    (P : VectorOSReconstructedWightman (-1) 𝒮) :
    (∀ (n : ℕ), 1 ≤ n → ∀ (α : Fin n → Fin 4) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → 𝒮 n α x = 0) ∧
    (∀ (n : ℕ), 1 ≤ n → ∀ (α : Fin n → Fin 4) (z : Fin n → Fin 4 → ℂ),
      z ∈ forward_tube_n n → P.E.H n α z = 0) ∧
    (∀ (n : ℕ), 1 ≤ n → ∀ (α : Fin n → Fin 4) (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ),
      P.W n α f = 0) ∧
    (OSVacuumNormalized 𝒮 → ∀ Φ : P.Hilbert, Φ = ⟪P.vacuum, Φ⟫_ℂ • P.vacuum) :=
  P.all_nPoint_eq_zero_of_diagonalStarStructure_of_eta_ne_one
    diagonalStarStructure_stdStarStructure (by norm_num)

lemma constOne_mem_posOrderedEuclidN {x₀ : Fin 4 → ℝ} (hx₀ : 0 < x₀ 0) :
    (fun _ : Fin 1 => x₀) ∈ posOrderedEuclidN 1 :=
  orderedEuclidN_pos_of_zero_pos 1 (mem_orderedEuclidN_one _) (fun _ => hx₀)

theorem osFieldPrependLM_osVacuumPre
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (α₀ : ι) (x₀ : Fin 4 → ℝ) (hx₀ : 0 < x₀ 0) :
    osFieldPrependLM D α₀ x₀ hx₀ (osVacuumPre D) =
      osBasisPre D ⟨1, (fun _ => α₀, ⟨fun _ => x₀, constOne_mem_posOrderedEuclidN hx₀⟩)⟩ := by
  unfold osFieldPrependLM osVacuumPre
  rw [osLiftConfigMap_osBasisPre]
  congr 1
  unfold osFieldPrependConfig osVacuumConfig
  congr 1
  ext i
  · fin_cases i
    rfl
  · fin_cases i
    rfl

theorem toOSHilbert_osFieldPrependLM_osVacuumPre_eq_zero_of_diag_twoPoint_eq_zero
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (hdiag : DiagonalStarStructure S) (c : ι)
    (hc2 : ∀ y ∈ orderedEuclidN 2, D.𝒮 2 (fun _ => c) y = 0)
    (x₀ : Fin 4 → ℝ) (hx₀ : 0 < x₀ 0) :
    toOSHilbert D (osFieldPrependLM D c x₀ hx₀ (osVacuumPre D)) = 0 := by
  rw [osFieldPrependLM_osVacuumPre]
  let y1 : posOrderedEuclidN 1 := ⟨fun _ => x₀, constOne_mem_posOrderedEuclidN hx₀⟩
  change osBasis D ⟨1, (fun _ => c, y1)⟩ = 0
  refine osBasis_eq_zero_of_osKernel_self_eq_zero D ?_
  rw [osKernel_onePoint_self_of_diagonalStarStructure hdiag D.𝒮 c y1,
      hc2 _ (osConcatPoint_mem_orderedEuclidN 1 1 y1.property y1.property), mul_zero]

theorem toOSHilbert_osFieldPrependLM_eq_zero_of_twoPoint_eq_zero
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (htrans : OSTranslationInvariant D.𝒮)
    (h2 : ∀ (β : Fin 2 → ι) (y : Fin 2 → Fin 4 → ℝ),
      y ∈ orderedEuclidN 2 → D.𝒮 2 β y = 0)
    (α₀ : ι) (x₀ : Fin 4 → ℝ) (hx₀ : 0 < x₀ 0) (Ψ : OSPreHilbertSpace D) :
    toOSHilbert D (osFieldPrependLM D α₀ x₀ hx₀ Ψ) = 0 := by
  classical
  conv_lhs => rw [osPreHilbert_eq_finsupp_sum_osBasisPre D Ψ]
  rw [map_finsuppSum, map_finsuppSum]
  unfold Finsupp.sum
  refine Finset.sum_eq_zero (fun A _ => ?_)
  dsimp only
  rw [LinearMap.map_smul, (toOSHilbert D).map_smul]
  unfold osFieldPrependLM
  rw [osLiftConfigMap_osBasisPre]
  change Ψ.toFinsupp A • osBasis D (osFieldPrependConfig α₀ x₀ hx₀ A) = 0
  have h_pos : 1 ≤ (osFieldPrependConfig α₀ x₀ hx₀ A).1 := by
    dsimp [osFieldPrependConfig]
    omega
  rw [osBasis_eq_zero_of_twoPoint_eq_zero D htrans h2 _ h_pos, smul_zero]

theorem inner_osVacuumPre_osFieldPrependLM_eq_zero_of_component_onePoint_osKernel_eq_zero
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (htrans : OSTranslationInvariant D.𝒮)
    (α₀ : ι)
    (h1 : ∀ (c : ι) (y : posOrderedEuclidN 1),
      S.C α₀ c ≠ 0 → osKernel S D.𝒮 ⟨1, (fun _ => c, y)⟩ ⟨1, (fun _ => c, y)⟩ = 0)
    (x₀ : Fin 4 → ℝ) (hx₀ : 0 < x₀ 0) (Ψ : OSPreHilbertSpace D) :
    ⟪osVacuumPre D, osFieldPrependLM D α₀ x₀ hx₀ Ψ⟫_ℂ = 0 := by
  classical
  conv_lhs => rw [osPreHilbert_eq_finsupp_sum_osBasisPre D Ψ]
  rw [map_finsuppSum]
  unfold Finsupp.sum
  rw [inner_sum]
  refine Finset.sum_eq_zero (fun A _ => ?_)
  dsimp only
  rw [LinearMap.map_smul, inner_smul_right, inner_osVacuumPre_osFieldPrependLM_osBasisPre]
  have h_ord : osPrependPoint A.1 x₀ A.2.2.val ∈ orderedEuclidN (A.1 + 1) :=
    posOrderedEuclidN_subset_orderedEuclidN (A.1 + 1)
      (osPrependPoint_mem_posOrderedEuclidN A.1 hx₀ A.2.2.property)
  have h_eq : D.𝒮 (A.1 + 1) (Fin.cons α₀ A.2.1) (osPrependPoint A.1 x₀ A.2.2.val) = 0 := by
    rw [← schwinger_congr_n D.𝒮 (Nat.add_comm 1 A.1)]
    have h_ord' : osPrependPoint A.1 x₀ A.2.2.val ∘ finCongr (Nat.add_comm 1 A.1) ∈
        orderedEuclidN (1 + A.1) := by
      intro i hi
      have hi' : (finCongr (Nat.add_comm 1 A.1) i).val + 1 < A.1 + 1 := by
        dsimp [finCongr]
        omega
      exact h_ord (finCongr (Nat.add_comm 1 A.1) i) hi'
    exact schwinger_one_add_eq_zero_of_component_onePoint_osKernel_eq_zero D htrans α₀ h1 A.1
      (Fin.cons α₀ A.2.1 ∘ finCongr (Nat.add_comm 1 A.1)) rfl h_ord'
  rw [h_eq, mul_zero]

theorem schwinger_one_add_eq_zero_of_last_component_onePoint_osKernel_eq_zero
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (htrans : OSTranslationInvariant D.𝒮)
    (hdiag : DiagonalStarStructure S) (c : ι)
    (h1 : ∀ y : posOrderedEuclidN 1,
      osKernel S D.𝒮 ⟨1, (fun _ => c, y)⟩ ⟨1, (fun _ => c, y)⟩ = 0)
    (j : ℕ) (α : Fin (1 + j) → ι)
    (hα_last : α (Fin.rev (Fin.castAdd j 0)) = c)
    {x : Fin (1 + j) → Fin 4 → ℝ} (hx : x ∈ orderedEuclidN (1 + j)) :
    D.𝒮 (1 + j) α x = 0 := by
  rw [← star_eq_zero, D.hermiticity (1 + j) α x hx]
  refine Finset.sum_eq_zero (fun β _ => ?_)
  by_cases hβ : β (Fin.rev (Fin.castAdd j 0)) = c
  · have h_zero : D.𝒮 (1 + j) (β ∘ Fin.rev) (euclidTimeReflectRev (1 + j) x) = 0 := by
      refine schwinger_one_add_eq_zero_of_component_onePoint_osKernel_eq_zero D htrans c
        (fun b y hcb => ?_) j (β ∘ Fin.rev) hβ
        (euclidTimeReflectRev_mem_orderedEuclidN (1 + j) hx)
      have hbc : c = b := by
        by_contra hne
        exact hcb (hdiag c b hne)
      subst hbc
      exact h1 y
    rw [h_zero, mul_zero]
  · have h_prod : (∏ i : Fin (1 + j), S.C (α i) (β i)) = 0 := by
      refine Finset.prod_eq_zero (Finset.mem_univ (Fin.rev (Fin.castAdd j 0))) ?_
      rw [hα_last]
      exact hdiag c (β (Fin.rev (Fin.castAdd j 0))) (Ne.symm hβ)
    rw [h_prod, zero_mul]

theorem schwinger_eq_zero_of_first_or_last_component_diag_twoPoint_eq_zero
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (htrans : OSTranslationInvariant D.𝒮)
    (hdiag : DiagonalStarStructure S) (c : ι)
    (hc2 : ∀ y ∈ orderedEuclidN 2, D.𝒮 2 (fun _ => c) y = 0)
    (n : ℕ) (hn : 1 ≤ n) (α : Fin n → ι)
    (hα : α ⟨0, hn⟩ = c ∨ α (Fin.rev ⟨0, hn⟩) = c)
    {x : Fin n → Fin 4 → ℝ} (hx : x ∈ orderedEuclidN n) :
    D.𝒮 n α x = 0 := by
  have hn_eq : 1 + (n - 1) = n := Nat.add_sub_of_le hn
  rw [← schwinger_congr_n D.𝒮 hn_eq α x]
  have hx' : x ∘ finCongr hn_eq ∈ orderedEuclidN (1 + (n - 1)) := by
    intro i hi
    have hi' : (finCongr hn_eq i).val + 1 < n := by
      dsimp [finCongr]
      omega
    exact hx (finCongr hn_eq i) hi'
  rcases hα with h_first | h_last
  · refine schwinger_one_add_eq_zero_of_diag_twoPoint_component_eq_zero D htrans hdiag c hc2
      (n - 1) (α ∘ finCongr hn_eq) ?_ hx'
    exact h_first
  · refine schwinger_one_add_eq_zero_of_last_component_onePoint_osKernel_eq_zero D htrans hdiag c
      (fun y => ?_) (n - 1) (α ∘ finCongr hn_eq) ?_ hx'
    · rw [osKernel_onePoint_self_of_diagonalStarStructure hdiag D.𝒮 c y,
          hc2 _ (osConcatPoint_mem_orderedEuclidN 1 1 y.property y.property), mul_zero]
    · have h_idx : finCongr hn_eq (Fin.rev (Fin.castAdd (n - 1) 0)) = Fin.rev ⟨0, hn⟩ := by
        ext
        dsimp [finCongr, Fin.rev]
        omega
      change α (finCongr hn_eq (Fin.rev (Fin.castAdd (n - 1) 0))) = c
      rwa [h_idx]

def diagImagMatrix : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.I, 0; 0, -Complex.I]

def diagImagSL2C : SL2C :=
  ⟨diagImagMatrix, by
    unfold diagImagMatrix
    rw [Matrix.det_fin_two_of]
    simp⟩

@[simp]
lemma diagImagSL2C_val : diagImagSL2C.1 = diagImagMatrix := rfl

def symplecticMatrix : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, -1; 1, 0]

def symplecticSL2C : SL2C :=
  ⟨symplecticMatrix, by
    unfold symplecticMatrix
    rw [Matrix.det_fin_two_of]
    ring⟩

@[simp]
lemma symplecticSL2C_val : symplecticSL2C.1 = symplecticMatrix := rfl

def finTwoFunEquiv (α : Type*) : (Fin 2 → α) ≃ (α × α) where
  toFun β := (β 0, β 1)
  invFun p := ![p.1, p.2]
  left_inv β := by
    ext i
    fin_cases i <;> rfl
  right_inv p := by
    rcases p with ⟨a, b⟩
    rfl

omit [Fintype ι] [DecidableEq ι] in
lemma finTwo_eq_vecCons (β : Fin 2 → ι) :
    β = ![β 0, β 1] := by
  ext i
  fin_cases i <;> rfl

omit [Fintype ι] [DecidableEq ι] in
lemma finTwo_comp_rev_vecCons (a b : ι) :
    (![a, b] : Fin 2 → ι) ∘ Fin.rev = ![b, a] := by
  ext i
  fin_cases i <;> rfl

omit [DecidableEq ι] in
lemma sum_fin_two_fun (F : (Fin 2 → ι) → ℂ) :
    (∑ β : Fin 2 → ι, F β) = ∑ a : ι, ∑ b : ι, F ![a, b] :=
  ((finTwoFunEquiv ι).symm.sum_comp F).symm.trans (Fintype.sum_prod_type _)

theorem finTwo_antisymm_of_diagImag_symplectic
    (F : (Fin 2 → Fin 2) → ℂ)
    (h_diag : ∀ α : Fin 2 → Fin 2,
      F α = ∑ β : Fin 2 → Fin 2, (∏ i : Fin 2, diagImagMatrix (α i) (β i)) * F β)
    (h_symp : ∀ α : Fin 2 → Fin 2,
      F α = ∑ β : Fin 2 → Fin 2, (∏ i : Fin 2, symplecticMatrix (α i) (β i)) * F β)
    (α : Fin 2 → Fin 2) :
    F α = (-1 : ℂ) * F (α ∘ Fin.rev) := by
  have h00 : F ![0, 0] = 0 := by
    have h := h_diag ![0, 0]
    rw [sum_fin_two_fun, Fin.sum_univ_two] at h
    simp only [Fin.sum_univ_two, Fin.prod_univ_two, Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val_one, diagImagMatrix, Matrix.of_apply, mul_zero,
      zero_mul, add_zero, Complex.I_mul_I] at h
    linear_combination (1 / 2 : ℂ) * h
  have h11 : F ![1, 1] = 0 := by
    have h := h_diag ![1, 1]
    rw [sum_fin_two_fun, Fin.sum_univ_two] at h
    simp only [Fin.sum_univ_two, Fin.prod_univ_two, Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val_one, diagImagMatrix, Matrix.of_apply, mul_zero,
      zero_mul, add_zero, zero_add, neg_mul_neg, Complex.I_mul_I] at h
    linear_combination (1 / 2 : ℂ) * h
  have h01 : F ![0, 1] = -F ![1, 0] := by
    have h := h_symp ![0, 1]
    rw [sum_fin_two_fun, Fin.sum_univ_two] at h
    simp only [Fin.sum_univ_two, Fin.prod_univ_two, Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val_one, symplecticMatrix, Matrix.of_apply,
      zero_mul, add_zero, zero_add, neg_one_mul] at h
    linear_combination h
  rw [finTwo_eq_vecCons α, finTwo_comp_rev_vecCons]
  generalize α 0 = a
  generalize α 1 = b
  fin_cases a <;> fin_cases b
  · change F ![0, 0] = -1 * F ![0, 0]; rw [h00]; ring
  · change F ![0, 1] = -1 * F ![1, 0]; rw [h01]; ring
  · change F ![1, 0] = -1 * F ![0, 1]; rw [h01]; ring
  · change F ![1, 1] = -1 * F ![1, 1]; rw [h11]; ring

theorem vladimirov_H_zero_twoPointIndexExchange_leftWeylRep
    (W : WightmanFamily (Fin 2))
    (hspec : SpectrumCondition W) (hP : PoincareCovariant leftWeylRep W)
    (α : Fin 2 → Fin 2) :
    vladimirov_H W 2 α 0 = (-1 : ℂ) * vladimirov_H W 2 (α ∘ Fin.rev) 0 := by
  refine finTwo_antisymm_of_diagImag_symplectic (fun β => vladimirov_H W 2 β 0)
    (fun β => ?_) (fun β => ?_) α
  · exact vladimirov_H_zero_complexCovariant leftWeylRep W hspec hP 2 diagImagSL2C 1 β
  · exact vladimirov_H_zero_complexCovariant leftWeylRep W hspec hP 2 symplecticSL2C 1 β

theorem vladimirov_H_zero_twoPointIndexExchange_rightWeylRep
    (W : WightmanFamily (Fin 2))
    (hspec : SpectrumCondition W) (hP : PoincareCovariant rightWeylRep W)
    (α : Fin 2 → Fin 2) :
    vladimirov_H W 2 α 0 = (-1 : ℂ) * vladimirov_H W 2 (α ∘ Fin.rev) 0 := by
  refine finTwo_antisymm_of_diagImag_symplectic (fun β => vladimirov_H W 2 β 0)
    (fun β => ?_) (fun β => ?_) α
  · exact vladimirov_H_zero_complexCovariant rightWeylRep W hspec hP 2 1 diagImagSL2C β
  · exact vladimirov_H_zero_complexCovariant rightWeylRep W hspec hP 2 1 symplecticSL2C β

lemma sum_directSumRep_inl_two {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁]
    [Fintype ι₂] [DecidableEq ι₂]
    (R₁ : HolomorphicLorentzRep ι₁) (R₂ : HolomorphicLorentzRep ι₂)
    (A B : SL2C) (F : (Fin 2 → ι₁ ⊕ ι₂) → ℂ) (α : Fin 2 → ι₁) :
    (∑ β : Fin 2 → ι₁ ⊕ ι₂,
      (∏ i : Fin 2, (directSumRep R₁ R₂).σ (A, B) (Sum.inl (α i)) (β i)) * F β) =
    ∑ β : Fin 2 → ι₁,
      (∏ i : Fin 2, R₁.σ (A, B) (α i) (β i)) * F (Sum.inl ∘ β) := by
  rw [sum_fin_two_fun (ι := ι₁ ⊕ ι₂), sum_fin_two_fun (ι := ι₁)]
  simp only [Fintype.sum_sum_type, Fin.prod_univ_two, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  have h_zero : ∀ x : ι₁, ∀ y : ι₂,
      (directSumRep R₁ R₂).σ (A, B) (Sum.inl x) (Sum.inr y) = 0 := fun _ _ => rfl
  have h_inl : ∀ x y : ι₁,
      (directSumRep R₁ R₂).σ (A, B) (Sum.inl x) (Sum.inl y) = R₁.σ (A, B) x y := fun _ _ => rfl
  simp only [h_zero, h_inl, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
  refine Finset.sum_congr rfl (fun b₀ _ => Finset.sum_congr rfl (fun b₁ _ => ?_))
  congr 1
  congr 1
  ext i
  fin_cases i <;> rfl

lemma sum_directSumRep_inr_two {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁]
    [Fintype ι₂] [DecidableEq ι₂]
    (R₁ : HolomorphicLorentzRep ι₁) (R₂ : HolomorphicLorentzRep ι₂)
    (A B : SL2C) (F : (Fin 2 → ι₁ ⊕ ι₂) → ℂ) (α : Fin 2 → ι₂) :
    (∑ β : Fin 2 → ι₁ ⊕ ι₂,
      (∏ i : Fin 2, (directSumRep R₁ R₂).σ (A, B) (Sum.inr (α i)) (β i)) * F β) =
    ∑ β : Fin 2 → ι₂,
      (∏ i : Fin 2, R₂.σ (A, B) (α i) (β i)) * F (Sum.inr ∘ β) := by
  rw [sum_fin_two_fun (ι := ι₁ ⊕ ι₂), sum_fin_two_fun (ι := ι₂)]
  simp only [Fintype.sum_sum_type, Fin.prod_univ_two, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  have h_zero : ∀ x : ι₂, ∀ y : ι₁,
      (directSumRep R₁ R₂).σ (A, B) (Sum.inr x) (Sum.inl y) = 0 := fun _ _ => rfl
  have h_inr : ∀ x y : ι₂,
      (directSumRep R₁ R₂).σ (A, B) (Sum.inr x) (Sum.inr y) = R₂.σ (A, B) x y := fun _ _ => rfl
  simp only [h_zero, h_inr, mul_zero, zero_mul, Finset.sum_const_zero, zero_add]
  refine Finset.sum_congr rfl (fun b₀ _ => Finset.sum_congr rfl (fun b₁ _ => ?_))
  congr 1
  congr 1
  ext i
  fin_cases i <;> rfl

theorem vladimirov_H_zero_diracRep_inl_inr_eq_zero
    (W : WightmanFamily (Fin 2 ⊕ Fin 2))
    (hspec : SpectrumCondition W) (hP : PoincareCovariant diracRep W)
    (a b : Fin 2) :
    vladimirov_H W 2 ![Sum.inl a, Sum.inr b] 0 = 0 := by
  have h_cov := vladimirov_H_zero_complexCovariant diracRep W hspec hP 2 (-1) 1
    ![Sum.inl a, Sum.inr b]
  have h_prod : ∀ β : Fin 2 → Fin 2 ⊕ Fin 2,
      (∏ i : Fin 2, diracRep.σ (-1, 1) (![Sum.inl a, Sum.inr b] i) (β i)) =
        if β = ![Sum.inl a, Sum.inr b] then -1 else 0 := by
    intro β
    rw [Fin.prod_univ_two]
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
    have h0 : diracRep.σ (-1, 1) (Sum.inl a) (β 0) =
        if β 0 = Sum.inl a then -1 else 0 := by
      rcases hβ0 : β 0 with x | x
      · change (-1 : SL2C).1 a x = if Sum.inl x = Sum.inl a then -1 else 0
        by_cases hax : x = a
        · subst hax; simp
        · have hne : a ≠ x := Ne.symm hax
          simp [hax, Matrix.one_apply_ne hne]
      · simp [diracRep, directSumRep]
    have h1 : diracRep.σ (-1, 1) (Sum.inr b) (β 1) =
        if β 1 = Sum.inr b then 1 else 0 := by
      rcases hβ1 : β 1 with y | y
      · simp [diracRep, directSumRep]
      · change (1 : SL2C).1 b y = if Sum.inr y = Sum.inr b then 1 else 0
        by_cases hby : y = b
        · subst hby; simp
        · have hne : b ≠ y := Ne.symm hby
          simp [hby, Matrix.one_apply_ne hne]
    rw [h0, h1]
    by_cases hβ : β = ![Sum.inl a, Sum.inr b]
    · subst hβ; simp
    · rw [if_neg hβ]
      by_cases h0' : β 0 = Sum.inl a
      · have h1' : β 1 ≠ Sum.inr b := by
          intro hc
          apply hβ
          rw [finTwo_eq_vecCons β, h0', hc]
        simp [h0', h1']
      · simp [h0']
  simp_rw [h_prod, ite_mul, neg_one_mul, zero_mul] at h_cov
  rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _)] at h_cov
  linear_combination (1 / 2 : ℂ) * h_cov

theorem vladimirov_H_zero_diracRep_inr_inl_eq_zero
    (W : WightmanFamily (Fin 2 ⊕ Fin 2))
    (hspec : SpectrumCondition W) (hP : PoincareCovariant diracRep W)
    (a b : Fin 2) :
    vladimirov_H W 2 ![Sum.inr a, Sum.inl b] 0 = 0 := by
  have h_cov := vladimirov_H_zero_complexCovariant diracRep W hspec hP 2 (-1) 1
    ![Sum.inr a, Sum.inl b]
  have h_prod : ∀ β : Fin 2 → Fin 2 ⊕ Fin 2,
      (∏ i : Fin 2, diracRep.σ (-1, 1) (![Sum.inr a, Sum.inl b] i) (β i)) =
        if β = ![Sum.inr a, Sum.inl b] then -1 else 0 := by
    intro β
    rw [Fin.prod_univ_two]
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
    have h0 : diracRep.σ (-1, 1) (Sum.inr a) (β 0) =
        if β 0 = Sum.inr a then 1 else 0 := by
      rcases hβ0 : β 0 with x | x
      · simp [diracRep, directSumRep]
      · change (1 : SL2C).1 a x = if Sum.inr x = Sum.inr a then 1 else 0
        by_cases hax : x = a
        · subst hax; simp
        · have hne : a ≠ x := Ne.symm hax
          simp [hax, Matrix.one_apply_ne hne]
    have h1 : diracRep.σ (-1, 1) (Sum.inl b) (β 1) =
        if β 1 = Sum.inl b then -1 else 0 := by
      rcases hβ1 : β 1 with y | y
      · change (-1 : SL2C).1 b y = if Sum.inl y = Sum.inl b then -1 else 0
        by_cases hby : y = b
        · subst hby; simp
        · have hne : b ≠ y := Ne.symm hby
          simp [hby, Matrix.one_apply_ne hne]
      · simp [diracRep, directSumRep]
    rw [h0, h1]
    by_cases hβ : β = ![Sum.inr a, Sum.inl b]
    · subst hβ; simp
    · rw [if_neg hβ]
      by_cases h0' : β 0 = Sum.inr a
      · have h1' : β 1 ≠ Sum.inl b := by
          intro hc
          apply hβ
          rw [finTwo_eq_vecCons β, h0', hc]
        simp [h0', h1']
      · simp [h0']
  simp_rw [h_prod, ite_mul, neg_one_mul, zero_mul] at h_cov
  rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _)] at h_cov
  linear_combination (1 / 2 : ℂ) * h_cov

theorem vladimirov_H_zero_twoPointIndexExchange_diracRep
    (W : WightmanFamily (Fin 2 ⊕ Fin 2))
    (hspec : SpectrumCondition W) (hP : PoincareCovariant diracRep W)
    (α : Fin 2 → Fin 2 ⊕ Fin 2) :
    vladimirov_H W 2 α 0 = (-1 : ℂ) * vladimirov_H W 2 (α ∘ Fin.rev) 0 := by
  have h_inl : ∀ γ : Fin 2 → Fin 2,
      vladimirov_H W 2 (Sum.inl ∘ γ) 0 =
        (-1 : ℂ) * vladimirov_H W 2 (Sum.inl ∘ (γ ∘ Fin.rev)) 0 := by
    refine finTwo_antisymm_of_diagImag_symplectic (fun γ => vladimirov_H W 2 (Sum.inl ∘ γ) 0)
      (fun γ => ?_) (fun γ => ?_)
    · have h := vladimirov_H_zero_complexCovariant diracRep W hspec hP 2
        diagImagSL2C 1 (Sum.inl ∘ γ)
      rw [h]
      exact sum_directSumRep_inl_two leftWeylRep rightWeylRep diagImagSL2C 1
        (fun β => vladimirov_H W 2 β 0) γ
    · have h := vladimirov_H_zero_complexCovariant diracRep W hspec hP 2
        symplecticSL2C 1 (Sum.inl ∘ γ)
      rw [h]
      exact sum_directSumRep_inl_two leftWeylRep rightWeylRep symplecticSL2C 1
        (fun β => vladimirov_H W 2 β 0) γ
  have h_inr : ∀ γ : Fin 2 → Fin 2,
      vladimirov_H W 2 (Sum.inr ∘ γ) 0 =
        (-1 : ℂ) * vladimirov_H W 2 (Sum.inr ∘ (γ ∘ Fin.rev)) 0 := by
    refine finTwo_antisymm_of_diagImag_symplectic (fun γ => vladimirov_H W 2 (Sum.inr ∘ γ) 0)
      (fun γ => ?_) (fun γ => ?_)
    · have h := vladimirov_H_zero_complexCovariant diracRep W hspec hP 2
        1 diagImagSL2C (Sum.inr ∘ γ)
      rw [h]
      exact sum_directSumRep_inr_two leftWeylRep rightWeylRep 1 diagImagSL2C
        (fun β => vladimirov_H W 2 β 0) γ
    · have h := vladimirov_H_zero_complexCovariant diracRep W hspec hP 2
        1 symplecticSL2C (Sum.inr ∘ γ)
      rw [h]
      exact sum_directSumRep_inr_two leftWeylRep rightWeylRep 1 symplecticSL2C
        (fun β => vladimirov_H W 2 β 0) γ
  rw [finTwo_eq_vecCons α, finTwo_comp_rev_vecCons]
  rcases h0 : α 0 with a | a <;> rcases h1 : α 1 with b | b
  · have h := h_inl ![a, b]
    have h_l : ((Sum.inl : Fin 2 → Fin 2 ⊕ Fin 2) ∘ (![a, b] : Fin 2 → Fin 2)) =
        ![Sum.inl a, Sum.inl b] := by
      ext i; fin_cases i <;> rfl
    have h_r : ((Sum.inl : Fin 2 → Fin 2 ⊕ Fin 2) ∘
        ((![a, b] : Fin 2 → Fin 2) ∘ Fin.rev)) = ![Sum.inl b, Sum.inl a] := by
      ext i; fin_cases i <;> rfl
    rwa [h_l, h_r] at h
  · rw [vladimirov_H_zero_diracRep_inl_inr_eq_zero W hspec hP a b,
        vladimirov_H_zero_diracRep_inr_inl_eq_zero W hspec hP b a, mul_zero]
  · rw [vladimirov_H_zero_diracRep_inr_inl_eq_zero W hspec hP a b,
        vladimirov_H_zero_diracRep_inl_inr_eq_zero W hspec hP b a, mul_zero]
  · have h := h_inr ![a, b]
    have h_l : ((Sum.inr : Fin 2 → Fin 2 ⊕ Fin 2) ∘ (![a, b] : Fin 2 → Fin 2)) =
        ![Sum.inr a, Sum.inr b] := by
      ext i; fin_cases i <;> rfl
    have h_r : ((Sum.inr : Fin 2 → Fin 2 ⊕ Fin 2) ∘
        ((![a, b] : Fin 2 → Fin 2) ∘ Fin.rev)) = ![Sum.inr b, Sum.inr a] := by
      ext i; fin_cases i <;> rfl
    rwa [h_l, h_r] at h

omit [Fintype ι] [DecidableEq ι] in
theorem wightman_twoPointIndexExchange_of_vladimirov_H_zero
    {W : WightmanFamily ι} {ε : ℂ} (hspec : SpectrumCondition W)
    (h_exch : ∀ α : Fin 2 → ι, vladimirov_H W 2 α 0 = ε * vladimirov_H W 2 (α ∘ Fin.rev) 0)
    (α : Fin 2 → ι) (f : SchwartzMap (Fin 2 → Fin 4 → ℝ) ℂ) :
    W 2 α f = ε * W 2 (α ∘ Fin.rev) f := by
  rw [W_n_eq_vladimirov_H_zero_mul_integral hspec 2 α f,
      W_n_eq_vladimirov_H_zero_mul_integral hspec 2 (α ∘ Fin.rev) f,
      h_exch α, mul_assoc]

omit [Fintype ι] [DecidableEq ι] in
theorem distributionalTwoPointSpinExchange_of_vladimirov_H_zero
    {W : WightmanFamily ι} {ε : ℂ} (hspec : SpectrumCondition W)
    (h_exch : ∀ α : Fin 2 → ι, vladimirov_H W 2 α 0 = ε * vladimirov_H W 2 (α ∘ Fin.rev) 0) :
    DistributionalTwoPointSpinExchange ε W := by
  intro α f f' _hf_jost hf'_rev
  rw [W_n_eq_vladimirov_H_zero_mul_integral hspec 2 α f,
      W_n_eq_vladimirov_H_zero_mul_integral hspec 2 (α ∘ Fin.rev) f',
      h_exch α]
  have h_eq : (fun x : Fin 2 → Fin 4 → ℝ => f x) =
      fun x => f' (fun i => x (Fin.rev i)) := by
    ext x
    exact (hf'_rev x).symm
  have h_int : (∫ x : Fin 2 → Fin 4 → ℝ, f x) = ∫ x : Fin 2 → Fin 4 → ℝ, f' x := by
    conv_lhs => rw [h_eq]
    exact integral_comp_rev 2 f'
  rw [h_int, mul_assoc]

theorem vladimirov_twoPointSpinExchange_of_vladimirov_H_zero
    (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι) {ε : ℂ}
    (hspec : SpectrumCondition W) (hP : PoincareCovariant R W)
    (h_exch : ∀ α : Fin 2 → ι, vladimirov_H W 2 α 0 = ε * vladimirov_H W 2 (α ∘ Fin.rev) 0) :
    TwoPointSpinExchange ε (vladimirovTubeExtension R W hspec hP) := by
  intro α z _hz
  change vladimirov_H W 2 α (-(z ∘ Fin.rev)) = ε * vladimirov_H W 2 (α ∘ Fin.rev) z
  rw [vladimirov_H_eq_zero_eval hspec 2 α (-(z ∘ Fin.rev)),
      vladimirov_H_eq_zero_eval hspec 2 (α ∘ Fin.rev) z]
  exact h_exch α

omit [Fintype ι] [DecidableEq ι] in
theorem vladimirovSchwinger_euclidTwoPointIndexExchange_of_vladimirov_H_zero
    {W : WightmanFamily ι} {ε : ℂ} (hspec : SpectrumCondition W)
    (h_exch : ∀ α : Fin 2 → ι, vladimirov_H W 2 α 0 = ε * vladimirov_H W 2 (α ∘ Fin.rev) 0) :
    EuclidTwoPointIndexExchange ε (vladimirovSchwinger W) := by
  intro α x _hx
  rw [vladimirovSchwinger_eq_zero_eval hspec 2 α x,
      vladimirovSchwinger_eq_zero_eval hspec 2 (α ∘ Fin.rev) x]
  exact h_exch α

omit [Fintype ι] [DecidableEq ι] in
theorem spin_statistics_of_vladimirov_H_zero_twoPointIndexExchange
    {W : WightmanFamily ι} {η ε : ℂ}
    (hspec : SpectrumCondition W) (hloc : WeakLocality η W)
    (h_exch : ∀ α : Fin 2 → ι, vladimirov_H W 2 α 0 = ε * vladimirov_H W 2 (α ∘ Fin.rev) 0)
    (h_nondeg : ∃ (α : Fin 2 → ι) (f : SchwartzMap (Fin 2 → Fin 4 → ℝ) ℂ), W 2 α f ≠ 0) :
    η = ε := by
  rcases h_nondeg with ⟨α, f, hf⟩
  have hH_ne : vladimirov_H W 2 α 0 ≠ 0 := by
    intro h0
    apply hf
    rw [W_n_eq_vladimirov_H_zero_mul_integral hspec 2 α f, h0, zero_mul]
  have h_loc := vladimirov_H_zero_weakLocality hspec hloc 2 (α ∘ Fin.rev)
  rw [two_mul_two_sub_one_div_two, pow_one] at h_loc
  have h_rev : (α ∘ Fin.rev) ∘ Fin.rev = α := by
    ext i; simp [Fin.rev_rev]
  rw [h_rev] at h_loc
  have h_sp := h_exch (α ∘ Fin.rev)
  rw [h_rev] at h_sp
  exact mul_right_cancel₀ hH_ne (h_loc.symm.trans h_sp)

omit [Fintype ι] [DecidableEq ι] in
theorem wightman_twoPoint_eq_zero_of_vladimirov_H_zero_twoPointIndexExchange
    {W : WightmanFamily ι} {η ε : ℂ}
    (hspec : SpectrumCondition W) (hloc : WeakLocality η W)
    (h_exch : ∀ α : Fin 2 → ι, vladimirov_H W 2 α 0 = ε * vladimirov_H W 2 (α ∘ Fin.rev) 0)
    (h_wrong : η ≠ ε)
    (α : Fin 2 → ι) (f : SchwartzMap (Fin 2 → Fin 4 → ℝ) ℂ) :
    W 2 α f = 0 := by
  by_contra h_ne
  exact h_wrong
    (spin_statistics_of_vladimirov_H_zero_twoPointIndexExchange hspec hloc h_exch ⟨α, f, h_ne⟩)

theorem leftWeyl_wightman_spin_statistics_unconditional
    (W : WightmanFamily (Fin 2)) {η : ℂ}
    (hspec : SpectrumCondition W) (hP : PoincareCovariant leftWeylRep W)
    (hloc : WeakLocality η W)
    (h_nondeg : ∃ (α : Fin 2 → Fin 2)
      (f : SchwartzMap (Fin 2 → Fin 4 → ℝ) ℂ), W 2 α f ≠ 0) :
    η = -1 :=
  spin_statistics_of_vladimirov_H_zero_twoPointIndexExchange hspec hloc
    (vladimirov_H_zero_twoPointIndexExchange_leftWeylRep W hspec hP) h_nondeg

theorem rightWeyl_wightman_spin_statistics_unconditional
    (W : WightmanFamily (Fin 2)) {η : ℂ}
    (hspec : SpectrumCondition W) (hP : PoincareCovariant rightWeylRep W)
    (hloc : WeakLocality η W)
    (h_nondeg : ∃ (α : Fin 2 → Fin 2)
      (f : SchwartzMap (Fin 2 → Fin 4 → ℝ) ℂ), W 2 α f ≠ 0) :
    η = -1 :=
  spin_statistics_of_vladimirov_H_zero_twoPointIndexExchange hspec hloc
    (vladimirov_H_zero_twoPointIndexExchange_rightWeylRep W hspec hP) h_nondeg

theorem dirac_wightman_spin_statistics_unconditional
    (W : WightmanFamily (Fin 2 ⊕ Fin 2)) {η : ℂ}
    (hspec : SpectrumCondition W) (hP : PoincareCovariant diracRep W)
    (hloc : WeakLocality η W)
    (h_nondeg : ∃ (α : Fin 2 → Fin 2 ⊕ Fin 2)
      (f : SchwartzMap (Fin 2 → Fin 4 → ℝ) ℂ), W 2 α f ≠ 0) :
    η = -1 :=
  spin_statistics_of_vladimirov_H_zero_twoPointIndexExchange hspec hloc
    (vladimirov_H_zero_twoPointIndexExchange_diracRep W hspec hP) h_nondeg

theorem leftWeyl_os_spin_statistics_unconditional
    {S : StarStructure leftWeylRep} {η : ℂ} {𝒮 : SchwingerFamily (Fin 2)}
    (P : OSReconstructedWightman leftWeylRep S η 𝒮)
    (h_nondeg : ∃ (α : Fin 2 → Fin 2)
      (f : SchwartzMap (Fin 2 → Fin 4 → ℝ) ℂ), P.W 2 α f ≠ 0) :
    η = -1 :=
  leftWeyl_wightman_spin_statistics_unconditional P.W P.spectrum P.poincare P.weakLocality h_nondeg

theorem rightWeyl_os_spin_statistics_unconditional
    {S : StarStructure rightWeylRep} {η : ℂ} {𝒮 : SchwingerFamily (Fin 2)}
    (P : OSReconstructedWightman rightWeylRep S η 𝒮)
    (h_nondeg : ∃ (α : Fin 2 → Fin 2)
      (f : SchwartzMap (Fin 2 → Fin 4 → ℝ) ℂ), P.W 2 α f ≠ 0) :
    η = -1 :=
  rightWeyl_wightman_spin_statistics_unconditional P.W P.spectrum P.poincare P.weakLocality h_nondeg

theorem dirac_os_spin_statistics_unconditional
    {η : ℂ} {𝒮 : SchwingerFamily (Fin 2 ⊕ Fin 2)}
    (P : DiracOSReconstructedWightman η 𝒮)
    (h_nondeg : ∃ (α : Fin 2 → Fin 2 ⊕ Fin 2)
      (f : SchwartzMap (Fin 2 → Fin 4 → ℝ) ℂ), P.W 2 α f ≠ 0) :
    η = -1 :=
  dirac_wightman_spin_statistics_unconditional P.W P.spectrum P.poincare P.weakLocality h_nondeg

def finAppendRevEquiv (j k : ℕ) :
    ((Fin j → Fin 4 → ℝ) × (Fin k → Fin 4 → ℝ)) ≃ᵐ (Fin (j + k) → Fin 4 → ℝ) where
  toEquiv := {
    toFun := fun p m => Fin.addCases (fun i => p.1 (Fin.rev i)) p.2 m
    invFun := fun x => (fun i => x (Fin.castAdd k (Fin.rev i)), fun i => x (Fin.natAdd j i))
    left_inv := fun ⟨y, z⟩ => by
      ext i m
      · simp [Fin.addCases_left, Fin.rev_rev]
      · simp [Fin.addCases_right]
    right_inv := fun x => by
      ext m
      refine Fin.addCases (fun i => ?_) (fun i => ?_) m
      · simp [Fin.addCases_left, Fin.rev_rev]
      · simp [Fin.addCases_right]
  }
  measurable_toFun := by
    refine (continuous_pi fun m => ?_).measurable
    refine Fin.addCases (fun i => ?_) (fun i => ?_) m
    · dsimp
      simp_rw [Fin.addCases_left]
      exact (continuous_apply (Fin.rev i)).comp continuous_fst
    · dsimp
      simp_rw [Fin.addCases_right]
      exact (continuous_apply i).comp continuous_snd
  measurable_invFun := by
    refine Measurable.prodMk ?_ ?_
    · exact measurable_pi_lambda _ (fun i => measurable_pi_apply (Fin.castAdd k (Fin.rev i)))
    · exact measurable_pi_lambda _ (fun i => measurable_pi_apply (Fin.natAdd j i))

lemma continuous_finAppendRevEquiv (j k : ℕ) :
    Continuous (finAppendRevEquiv j k) := by
  refine continuous_pi (fun m => ?_)
  refine Fin.addCases (fun i => ?_) (fun i => ?_) m
  · dsimp [finAppendRevEquiv]
    simp_rw [Fin.addCases_left]
    exact (continuous_apply (Fin.rev i)).comp continuous_fst
  · dsimp [finAppendRevEquiv]
    simp_rw [Fin.addCases_right]
    exact (continuous_apply i).comp continuous_snd

lemma measurePreserving_finAppendRevEquiv (j k : ℕ) :
    MeasurePreserving (finAppendRevEquiv j k) volume volume := by
  refine ⟨(finAppendRevEquiv j k).measurable, ?_⟩
  refine (MeasureTheory.Measure.pi_eq fun s hs => ?_).symm
  rw [MeasureTheory.Measure.map_apply (finAppendRevEquiv j k).measurable
    (MeasurableSet.univ_pi hs)]
  have h_pre : (finAppendRevEquiv j k) ⁻¹' (Set.pi Set.univ s) =
      (Set.pi Set.univ (fun i : Fin j => s (Fin.castAdd k (Fin.rev i)))) ×ˢ
      (Set.pi Set.univ (fun i : Fin k => s (Fin.natAdd j i))) := by
    ext ⟨y, z⟩
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, Set.mem_prod]
    constructor
    · intro h
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simpa [finAppendRevEquiv, Fin.addCases_left] using h (Fin.castAdd k (Fin.rev i))
      · simpa [finAppendRevEquiv, Fin.addCases_right] using h (Fin.natAdd j i)
    · rintro ⟨h1, h2⟩ m
      refine Fin.addCases (fun i => ?_) (fun i => ?_) m
      · have := h1 (Fin.rev i)
        simpa [finAppendRevEquiv, Fin.addCases_left, Fin.rev_rev] using this
      · simpa [finAppendRevEquiv, Fin.addCases_right] using h2 i
  rw [h_pre, MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod]
  have h1 : (volume : MeasureTheory.Measure (Fin j → Fin 4 → ℝ))
      (Set.pi Set.univ (fun i : Fin j => s (Fin.castAdd k (Fin.rev i)))) =
      ∏ i : Fin j, volume (s (Fin.castAdd k (Fin.rev i))) := by
    rw [MeasureTheory.volume_pi, MeasureTheory.Measure.pi_pi]
  have h2 : (volume : MeasureTheory.Measure (Fin k → Fin 4 → ℝ))
      (Set.pi Set.univ (fun i : Fin k => s (Fin.natAdd j i))) =
      ∏ i : Fin k, volume (s (Fin.natAdd j i)) := by
    rw [MeasureTheory.volume_pi, MeasureTheory.Measure.pi_pi]
  rw [h1, h2, Fin.prod_univ_add]
  congr 1
  exact Equiv.prod_comp Fin.revPerm (fun i : Fin j => volume (s (Fin.castAdd k i)))

lemma integral_split_rev_mul (j k : ℕ)
    (f : (Fin j → Fin 4 → ℝ) → ℂ) (g : (Fin k → Fin 4 → ℝ) → ℂ) :
    (∫ x : Fin (j + k) → Fin 4 → ℝ,
      f (fun i => x (Fin.castAdd k (Fin.rev i))) * g (fun i => x (Fin.natAdd j i))) =
    (∫ y : Fin j → Fin 4 → ℝ, f y) * (∫ z : Fin k → Fin 4 → ℝ, g z) := by
  have h_mp := measurePreserving_finAppendRevEquiv j k
  rw [← h_mp.integral_comp (finAppendRevEquiv j k).measurableEmbedding]
  have h_eq : (fun p : (Fin j → Fin 4 → ℝ) × (Fin k → Fin 4 → ℝ) =>
      f (fun i => finAppendRevEquiv j k p (Fin.castAdd k (Fin.rev i))) *
        g (fun i => finAppendRevEquiv j k p (Fin.natAdd j i))) =
      (fun p => f p.1 * g p.2) := by
    ext ⟨y, z⟩
    have hy : (fun i : Fin j => finAppendRevEquiv j k (y, z) (Fin.castAdd k (Fin.rev i))) = y := by
      ext i m
      simp [finAppendRevEquiv, Fin.addCases_left, Fin.rev_rev]
    have hz : (fun i : Fin k => finAppendRevEquiv j k (y, z) (Fin.natAdd j i)) = z := by
      ext i m
      simp [finAppendRevEquiv, Fin.addCases_right]
    rw [hy, hz]
  rw [h_eq, MeasureTheory.Measure.volume_eq_prod, MeasureTheory.integral_prod_mul]

def jostProductFun (j k : ℕ) (x : Fin (j + k) → Fin 4 → ℝ) : ℂ :=
  (starRingEnd ℂ) (jostSchwartz j (fun i => x (Fin.castAdd k (Fin.rev i)))) *
    jostSchwartz k (fun i => x (Fin.natAdd j i))

lemma jostProductFun_contDiff (j k : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (jostProductFun j k) := by
  have h_left : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Fin (j + k) → Fin 4 → ℝ =>
        (fun i : Fin j => x (Fin.castAdd k (Fin.rev i)))) :=
    contDiff_pi.mpr (fun i => contDiff_apply ℝ (Fin 4 → ℝ) (Fin.castAdd k (Fin.rev i)))
  have h_right : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Fin (j + k) → Fin 4 → ℝ =>
        (fun i : Fin k => x (Fin.natAdd j i))) :=
    contDiff_pi.mpr (fun i => contDiff_apply ℝ (Fin 4 → ℝ) (Fin.natAdd j i))
  exact (Complex.conjCLE.contDiff.comp ((jostBump_complex_contDiff j).comp h_left)).mul
    ((jostBump_complex_contDiff k).comp h_right)

lemma jostProductFun_hasCompactSupport (j k : ℕ) :
    HasCompactSupport (jostProductFun j k) := by
  refine HasCompactSupport.of_support_subset_isCompact
    (((jostBump_complex_hasCompactSupport j).isCompact.prod
      (jostBump_complex_hasCompactSupport k).isCompact).image
      (continuous_finAppendRevEquiv j k)) ?_
  intro x hx
  rw [Function.mem_support] at hx
  have h_left_ne : jostSchwartz j (fun i => x (Fin.castAdd k (Fin.rev i))) ≠ 0 := by
    intro h0
    apply hx
    simp [jostProductFun, h0]
  have h_right_ne : jostSchwartz k (fun i => x (Fin.natAdd j i)) ≠ 0 := by
    intro h0
    apply hx
    simp [jostProductFun, h0]
  refine ⟨((fun i => x (Fin.castAdd k (Fin.rev i))), (fun i => x (Fin.natAdd j i))),
    ⟨subset_tsupport _ h_left_ne, subset_tsupport _ h_right_ne⟩, ?_⟩
  exact (finAppendRevEquiv j k).toEquiv.right_inv x

def jostProductSchwartz (j k : ℕ) : SchwartzMap (Fin (j + k) → Fin 4 → ℝ) ℂ :=
  (jostProductFun_hasCompactSupport j k).toSchwartzMap (jostProductFun_contDiff j k)

@[simp]
lemma jostProductSchwartz_apply (j k : ℕ) (x : Fin (j + k) → Fin 4 → ℝ) :
    jostProductSchwartz j k x =
      (starRingEnd ℂ) (jostSchwartz j (fun i => x (Fin.castAdd k (Fin.rev i)))) *
        jostSchwartz k (fun i => x (Fin.natAdd j i)) := rfl

@[simp]
lemma star_jostSchwartz_apply (n : ℕ) (x : Fin n → Fin 4 → ℝ) :
    (starRingEnd ℂ) (jostSchwartz n x) = jostSchwartz n x := by
  rw [jostSchwartz_apply]
  exact Complex.conj_ofReal _

lemma integral_jostProductSchwartz_eq (j k : ℕ) :
    (∫ x : Fin (j + k) → Fin 4 → ℝ, jostProductSchwartz j k x) =
      (∫ y : Fin j → Fin 4 → ℝ, jostSchwartz j y) *
        (∫ z : Fin k → Fin 4 → ℝ, jostSchwartz k z) := by
  have h_eq : (fun x : Fin (j + k) → Fin 4 → ℝ => jostProductSchwartz j k x) =
      fun x => ((fun y => (starRingEnd ℂ) (jostSchwartz j y))
        (fun i => x (Fin.castAdd k (Fin.rev i)))) *
        ((fun z => jostSchwartz k z) (fun i => x (Fin.natAdd j i))) := rfl
  rw [h_eq, integral_split_rev_mul j k
    (fun y => (starRingEnd ℂ) (jostSchwartz j y))
    (fun z => jostSchwartz k z)]
  congr 1
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
  exact star_jostSchwartz_apply j y

@[simp]
lemma star_integral_jostSchwartz (n : ℕ) :
    (starRingEnd ℂ) (∫ y : Fin n → Fin 4 → ℝ, jostSchwartz n y) =
      ∫ y : Fin n → Fin 4 → ℝ, jostSchwartz n y := by
  rw [← integral_conj]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
  exact star_jostSchwartz_apply n y

def vladimirovKernel {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    (W : WightmanFamily ι) (j k : ℕ) (α : Fin j → ι) (α' : Fin k → ι) : ℂ :=
  ∑ β : Fin j → ι,
    (∏ i : Fin j, S.C (α i) (β i)) *
      vladimirov_H W (j + k) (Fin.append (β ∘ Fin.rev) α') 0

lemma osKernel_vladimirovSchwinger {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    {W : WightmanFamily ι} (hspec : SpectrumCondition W) (A B : OSConfig ι) :
    osKernel S (vladimirovSchwinger W) A B =
      vladimirovKernel S W A.1 B.1 A.2.1 B.2.1 := by
  unfold osKernel vladimirovKernel osConcatIdx
  refine Finset.sum_congr rfl (fun β _ => ?_)
  rw [vladimirovSchwinger_eq_zero_eval hspec]

def vladimirovSesquilinear {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    (W : WightmanFamily ι) (N : ℕ)
    (u v : ∀ j : ℕ, (Fin j → ι) → ℂ) : ℂ :=
  ∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
    ∑ α : Fin j → ι, ∑ α' : Fin k → ι,
      star (u j α) * v k α' * vladimirovKernel S W j k α α'

theorem vladimirov_H_zero_positivity {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    (W : WightmanFamily ι) (hspec : SpectrumCondition W) (hpos : Positivity S W)
    (N : ℕ) (u : ∀ j : ℕ, (Fin j → ι) → ℂ) :
    0 ≤ vladimirovSesquilinear S W N u u := by
  let I : ℕ → ℂ := fun j => ∫ y : Fin j → Fin 4 → ℝ, jostSchwartz j y
  let v : ∀ j : ℕ, (Fin j → ι) → ℂ := fun j α => u j α * (I j)⁻¹
  let F : ∀ j : ℕ, (Fin j → ι) → SchwartzMap (Fin j → Fin 4 → ℝ) ℂ :=
    fun j α => v j α • jostSchwartz j
  let G : ∀ j k : ℕ, (Fin j → ι) → (Fin k → ι) →
      SchwartzMap (Fin (j + k) → Fin 4 → ℝ) ℂ :=
    fun j k α α' => ((starRingEnd ℂ) (v j α) * v k α') • jostProductSchwartz j k
  have hG : ∀ j k α α' (x : Fin (j + k) → Fin 4 → ℝ),
      G j k α α' x =
        (starRingEnd ℂ) (F j α (fun i => x (Fin.castAdd k (Fin.rev i)))) *
          F k α' (fun i => x (Fin.natAdd j i)) := by
    intro j k α α' x
    simp only [F, G, _root_.smul_apply, smul_eq_mul, map_mul, jostProductSchwartz_apply]
    ring
  have h_pos := hpos N F G hG
  have h_term : ∀ j k (α : Fin j → ι) (α' : Fin k → ι) (β : Fin j → ι),
      (∏ i, S.C (α i) (β i)) * W (j + k) (Fin.append (β ∘ Fin.rev) α') (G j k α α') =
        star (u j α) * u k α' *
          ((∏ i, S.C (α i) (β i)) *
            vladimirov_H W (j + k) (Fin.append (β ∘ Fin.rev) α') 0) := by
    intro j k α α' β
    rw [W_n_eq_vladimirov_H_zero_mul_integral hspec (j + k) (Fin.append (β ∘ Fin.rev) α')
      (G j k α α')]
    have h_int : (∫ x : Fin (j + k) → Fin 4 → ℝ, G j k α α' x) = star (u j α) * u k α' := by
      change (∫ x : Fin (j + k) → Fin 4 → ℝ,
        ((starRingEnd ℂ) (v j α) * v k α') * jostProductSchwartz j k x) = _
      rw [MeasureTheory.integral_const_mul, integral_jostProductSchwartz_eq]
      dsimp [v, I]
      rw [map_mul, map_inv₀, star_integral_jostSchwartz j, ← Complex.star_def]
      have hj := integral_jostSchwartz_ne_zero j
      have hk := integral_jostSchwartz_ne_zero k
      calc (star (u j α) * (∫ y, jostSchwartz j y)⁻¹ *
            (u k α' * (∫ z, jostSchwartz k z)⁻¹)) *
            ((∫ y, jostSchwartz j y) * ∫ z, jostSchwartz k z)
        _ = star (u j α) * u k α' *
              ((∫ y, jostSchwartz j y)⁻¹ * ∫ y, jostSchwartz j y) *
              ((∫ z, jostSchwartz k z)⁻¹ * ∫ z, jostSchwartz k z) := by ring
        _ = star (u j α) * u k α' := by
              rw [inv_mul_cancel₀ hj, inv_mul_cancel₀ hk, mul_one, mul_one]
    rw [h_int]
    ring
  simp_rw [h_term, ← Finset.mul_sum] at h_pos
  exact h_pos

lemma vladimirovSesquilinear_linear_comb {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    (W : WightmanFamily ι) (N : ℕ)
    (u v : ∀ j : ℕ, (Fin j → ι) → ℂ) (z : ℂ) :
    vladimirovSesquilinear S W N
      (fun j α => z * u j α + v j α) (fun j α => z * u j α + v j α) =
      (star z * z) * vladimirovSesquilinear S W N u u +
      star z * vladimirovSesquilinear S W N u v +
      z * vladimirovSesquilinear S W N v u +
      vladimirovSesquilinear S W N v v := by
  unfold vladimirovSesquilinear
  have h_inner : ∀ j k (α : Fin j → ι) (α' : Fin k → ι),
      star (z * u j α + v j α) * (z * u k α' + v k α') * vladimirovKernel S W j k α α' =
        (star z * z) * (star (u j α) * u k α' * vladimirovKernel S W j k α α') +
        star z * (star (u j α) * v k α' * vladimirovKernel S W j k α α') +
        z * (star (v j α) * u k α' * vladimirovKernel S W j k α α') +
        (star (v j α) * v k α' * vladimirovKernel S W j k α α') := by
    intro j k α α'
    rw [star_add, star_mul']
    ring
  simp_rw [h_inner, Finset.sum_add_distrib, ← Finset.mul_sum]

lemma complex_eq_zero_of_forall_real_mul_add_nonneg {X D : ℂ}
    (h : ∀ t : ℝ, 0 ≤ (t : ℂ) * X + D) :
    X = 0 := by
  have h0 := Complex.nonneg_iff.mp (h 0)
  have h1 := Complex.nonneg_iff.mp (h 1)
  simp only [Complex.ofReal_zero, zero_mul, zero_add] at h0
  simp only [Complex.ofReal_one, one_mul, Complex.add_im] at h1
  have hD_im : D.im = 0 := h0.2.symm
  have hX_im : X.im = 0 := by linarith [h1.2]
  have hX_re : X.re = 0 := by
    by_contra hne
    have ht := (Complex.nonneg_iff.mp (h (-(D.re + 1) / X.re))).1
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      hX_im, mul_zero, sub_zero] at ht
    rw [div_mul_cancel₀ _ hne] at ht
    linarith
  exact Complex.ext hX_re hX_im

lemma complex_eq_zero_of_forall_star_mul_add_nonneg {A B D : ℂ}
    (h : ∀ z : ℂ, 0 ≤ star z * A + z * B + D) :
    A = 0 := by
  have h1 : A + B = 0 := by
    refine complex_eq_zero_of_forall_real_mul_add_nonneg (D := D) (fun t => ?_)
    have ht := h (t : ℂ)
    have h_eq : star (t : ℂ) * A + (t : ℂ) * B + D = (t : ℂ) * (A + B) + D := by
      rw [Complex.star_def, Complex.conj_ofReal]
      ring
    rwa [h_eq] at ht
  have h2 : Complex.I * (B - A) = 0 := by
    refine complex_eq_zero_of_forall_real_mul_add_nonneg (D := D) (fun t => ?_)
    have ht := h (Complex.I * (t : ℂ))
    have h_eq : star (Complex.I * (t : ℂ)) * A + (Complex.I * (t : ℂ)) * B + D =
        (t : ℂ) * (Complex.I * (B - A)) + D := by
      rw [star_mul', Complex.star_def, Complex.conj_I, Complex.conj_ofReal]
      ring
    rwa [h_eq] at ht
  have hI : Complex.I * (Complex.I * (B - A)) = -(B - A) := by
    rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]
  have h2' : -(B - A) = 0 := by
    rw [← hI, h2, mul_zero]
  linear_combination (1 / 2 : ℂ) * h1 + (1 / 2 : ℂ) * h2'

theorem vladimirovSesquilinear_eq_zero_of_diag_eq_zero
    {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    (W : WightmanFamily ι) (hspec : SpectrumCondition W) (hpos : Positivity S W)
    (N : ℕ) (u v : ∀ j : ℕ, (Fin j → ι) → ℂ)
    (hu : vladimirovSesquilinear S W N u u = 0) :
    vladimirovSesquilinear S W N u v = 0 := by
  refine complex_eq_zero_of_forall_star_mul_add_nonneg
    (B := vladimirovSesquilinear S W N v u)
    (D := vladimirovSesquilinear S W N v v) (fun z => ?_)
  have h := vladimirov_H_zero_positivity S W hspec hpos N (fun j α => z * u j α + v j α)
  rwa [vladimirovSesquilinear_linear_comb, hu, mul_zero, zero_add] at h

def vladimirovDelta (j₀ : ℕ) (α₀ : Fin j₀ → ι) (j : ℕ) (α : Fin j → ι) : ℂ :=
  if h : j = j₀ then (if h ▸ α = α₀ then 1 else 0) else 0

omit [Fintype ι] in
@[simp]
lemma star_vladimirovDelta (j₀ : ℕ) (α₀ : Fin j₀ → ι) (j : ℕ) (α : Fin j → ι) :
    star (vladimirovDelta j₀ α₀ j α) = vladimirovDelta j₀ α₀ j α := by
  dsimp [vladimirovDelta]
  split_ifs <;> simp

lemma sum_vladimirovDelta_mul (N j₀ : ℕ) (hj₀ : j₀ ≤ N) (α₀ : Fin j₀ → ι)
    (F : ∀ j : ℕ, (Fin j → ι) → ℂ) :
    (∑ j ∈ Finset.range (N + 1), ∑ α : Fin j → ι,
      vladimirovDelta j₀ α₀ j α * F j α) = F j₀ α₀ := by
  have h_inner : ∀ j : ℕ,
      (∑ α : Fin j → ι, vladimirovDelta j₀ α₀ j α * F j α) =
        if j = j₀ then F j₀ α₀ else 0 := by
    intro j
    by_cases hj : j = j₀
    · subst hj
      simp only [vladimirovDelta, ↓reduceDIte, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    · simp [vladimirovDelta, hj]
  simp_rw [h_inner]
  rw [Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr (Nat.lt_succ_of_le hj₀))]

lemma vladimirovSesquilinear_delta {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    (W : WightmanFamily ι) (N j₁ j₂ : ℕ) (hj₁ : j₁ ≤ N) (hj₂ : j₂ ≤ N)
    (α₁ : Fin j₁ → ι) (α₂ : Fin j₂ → ι) :
    vladimirovSesquilinear S W N
      (vladimirovDelta j₁ α₁) (vladimirovDelta j₂ α₂) =
      vladimirovKernel S W j₁ j₂ α₁ α₂ := by
  unfold vladimirovSesquilinear
  simp_rw [star_vladimirovDelta, mul_assoc]
  have h_k : ∀ j (α : Fin j → ι),
      (∑ k ∈ Finset.range (N + 1), ∑ α' : Fin k → ι,
        vladimirovDelta j₁ α₁ j α *
          (vladimirovDelta j₂ α₂ k α' * vladimirovKernel S W j k α α')) =
      vladimirovDelta j₁ α₁ j α * vladimirovKernel S W j j₂ α α₂ := by
    intro j α
    simp_rw [← Finset.mul_sum]
    congr 1
    exact sum_vladimirovDelta_mul N j₂ hj₂ α₂ (fun k α' => vladimirovKernel S W j k α α')
  have h_j : ∀ j,
      (∑ k ∈ Finset.range (N + 1), ∑ α : Fin j → ι, ∑ α' : Fin k → ι,
        vladimirovDelta j₁ α₁ j α *
          (vladimirovDelta j₂ α₂ k α' * vladimirovKernel S W j k α α')) =
      ∑ α : Fin j → ι, vladimirovDelta j₁ α₁ j α * vladimirovKernel S W j j₂ α α₂ := by
    intro j
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun α _ => h_k j α)
  simp_rw [h_j]
  exact sum_vladimirovDelta_mul N j₁ hj₁ α₁ (fun j α => vladimirovKernel S W j j₂ α α₂)

theorem vladimirovKernel_one_right_eq_zero_of_one_self_eq_zero
    {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    (W : WightmanFamily ι) (hspec : SpectrumCondition W) (hpos : Positivity S W)
    (c : ι) (hc : vladimirovKernel S W 1 1 (fun _ => c) (fun _ => c) = 0)
    (m : ℕ) (α' : Fin m → ι) :
    vladimirovKernel S W 1 m (fun _ => c) α' = 0 := by
  have h1 : 1 ≤ max 1 m := le_max_left 1 m
  have hm : m ≤ max 1 m := le_max_right 1 m
  rw [← vladimirovSesquilinear_delta S W (max 1 m) 1 m h1 hm (fun _ => c) α']
  refine vladimirovSesquilinear_eq_zero_of_diag_eq_zero S W hspec hpos (max 1 m)
    (vladimirovDelta 1 (fun _ => c)) (vladimirovDelta m α') ?_
  rw [vladimirovSesquilinear_delta S W (max 1 m) 1 1 h1 h1 (fun _ => c) (fun _ => c)]
  exact hc

theorem vladimirov_H_one_add_eq_sum_vladimirovKernel
    {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    (W : WightmanFamily ι) (hspec : SpectrumCondition W)
    (m : ℕ) (α : Fin (1 + m) → ι) :
    vladimirov_H W (1 + m) α 0 =
      ∑ c : ι, star (S.C (α (Fin.castAdd m 0)) c) *
        vladimirovKernel S W 1 m (fun _ => c) (fun i => α (Fin.natAdd 1 i)) := by
  have hx := euclidOrderedBasePoint_mem_orderedEuclidN (1 + m)
  have h := schwinger_one_add_eq_sum_osKernel S (vladimirovSchwinger W)
    (fun n β y _ a => vladimirovSchwinger_translation_invariant hspec n β y a) m α hx
  rw [vladimirovSchwinger_eq_zero_eval hspec (1 + m) α (euclidOrderedBasePoint (1 + m))] at h
  simp_rw [osKernel_vladimirovSchwinger S hspec] at h
  exact h

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_H_zero_congr_n {W : WightmanFamily ι} {n₁ n₂ : ℕ} (h : n₁ = n₂)
    (α : Fin n₂ → ι) :
    vladimirov_H W n₁ (α ∘ finCongr h) 0 = vladimirov_H W n₂ α 0 := by
  subst h
  rfl

theorem wightman_eq_zero_of_onePoint_vladimirovKernel_eq_zero
    {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    (W : WightmanFamily ι) (hspec : SpectrumCondition W) (hpos : Positivity S W)
    (h1 : ∀ c : ι, vladimirovKernel S W 1 1 (fun _ => c) (fun _ => c) = 0)
    (n : ℕ) (hn : 1 ≤ n) (α : Fin n → ι)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    W n α f = 0 := by
  rw [W_n_eq_vladimirov_H_zero_mul_integral hspec n α f]
  have hn_eq : 1 + (n - 1) = n := Nat.add_sub_of_le hn
  rw [← vladimirov_H_zero_congr_n hn_eq α,
      vladimirov_H_one_add_eq_sum_vladimirovKernel S W hspec (n - 1) (α ∘ finCongr hn_eq)]
  have h_sum : (∑ c : ι, star (S.C ((α ∘ finCongr hn_eq) (Fin.castAdd (n - 1) 0)) c) *
      vladimirovKernel S W 1 (n - 1) (fun _ => c)
        (fun i => (α ∘ finCongr hn_eq) (Fin.natAdd 1 i))) = 0 := by
    refine Finset.sum_eq_zero (fun c _ => ?_)
    rw [vladimirovKernel_one_right_eq_zero_of_one_self_eq_zero S W hspec hpos c (h1 c), mul_zero]
  rw [h_sum, zero_mul]

theorem wightman_eq_zero_of_twoPoint_eq_zero_of_positivity
    {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    (W : WightmanFamily ι) (hspec : SpectrumCondition W) (hpos : Positivity S W)
    (hW2 : ∀ (β : Fin 2 → ι) (f : SchwartzMap (Fin 2 → Fin 4 → ℝ) ℂ), W 2 β f = 0)
    (n : ℕ) (hn : 1 ≤ n) (α : Fin n → ι)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    W n α f = 0 := by
  refine wightman_eq_zero_of_onePoint_vladimirovKernel_eq_zero S W hspec hpos (fun c => ?_) n hn α f
  unfold vladimirovKernel
  refine Finset.sum_eq_zero (fun β _ => ?_)
  rw [vladimirov_H_eq_zero_of_wightman_eq_zero 2 _ (hW2 _) 0, mul_zero]

theorem spin_statistics_any_nPoint_of_vladimirov_H_zero_twoPointIndexExchange
    {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    (W : WightmanFamily ι) {η ε : ℂ}
    (hspec : SpectrumCondition W) (hloc : WeakLocality η W) (hpos : Positivity S W)
    (h_exch : ∀ α : Fin 2 → ι, vladimirov_H W 2 α 0 = ε * vladimirov_H W 2 (α ∘ Fin.rev) 0)
    (h_nondeg : ∃ (n : ℕ) (_ : 1 ≤ n) (α : Fin n → ι)
      (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ), W n α f ≠ 0) :
    η = ε := by
  by_contra h_wrong
  rcases h_nondeg with ⟨n, hn, α, f, hf⟩
  exact hf (wightman_eq_zero_of_twoPoint_eq_zero_of_positivity S W hspec hpos
    (wightman_twoPoint_eq_zero_of_vladimirov_H_zero_twoPointIndexExchange hspec hloc h_exch h_wrong)
    n hn α f)

theorem leftWeyl_os_spin_statistics_any_nPoint_unconditional
    {S : StarStructure leftWeylRep} {η : ℂ} {𝒮 : SchwingerFamily (Fin 2)}
    (P : OSReconstructedWightman leftWeylRep S η 𝒮)
    (h_nondeg : ∃ (n : ℕ) (_ : 1 ≤ n) (α : Fin n → Fin 2)
      (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ), P.W n α f ≠ 0) :
    η = -1 :=
  spin_statistics_any_nPoint_of_vladimirov_H_zero_twoPointIndexExchange S P.W
    P.spectrum P.weakLocality P.positivity
    (vladimirov_H_zero_twoPointIndexExchange_leftWeylRep P.W P.spectrum P.poincare) h_nondeg

theorem rightWeyl_os_spin_statistics_any_nPoint_unconditional
    {S : StarStructure rightWeylRep} {η : ℂ} {𝒮 : SchwingerFamily (Fin 2)}
    (P : OSReconstructedWightman rightWeylRep S η 𝒮)
    (h_nondeg : ∃ (n : ℕ) (_ : 1 ≤ n) (α : Fin n → Fin 2)
      (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ), P.W n α f ≠ 0) :
    η = -1 :=
  spin_statistics_any_nPoint_of_vladimirov_H_zero_twoPointIndexExchange S P.W
    P.spectrum P.weakLocality P.positivity
    (vladimirov_H_zero_twoPointIndexExchange_rightWeylRep P.W P.spectrum P.poincare) h_nondeg

theorem dirac_os_spin_statistics_any_nPoint_unconditional
    {η : ℂ} {𝒮 : SchwingerFamily (Fin 2 ⊕ Fin 2)}
    (P : DiracOSReconstructedWightman η 𝒮)
    (h_nondeg : ∃ (n : ℕ) (_ : 1 ≤ n) (α : Fin n → Fin 2 ⊕ Fin 2)
      (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ), P.W n α f ≠ 0) :
    η = -1 :=
  spin_statistics_any_nPoint_of_vladimirov_H_zero_twoPointIndexExchange diracStarStructure P.W
    P.spectrum P.weakLocality P.positivity
    (vladimirov_H_zero_twoPointIndexExchange_diracRep P.W P.spectrum P.poincare) h_nondeg

theorem dirac_os_wrong_statistics_wightman_all_nPoint_eq_zero
    {η : ℂ} {𝒮 : SchwingerFamily (Fin 2 ⊕ Fin 2)}
    (P : DiracOSReconstructedWightman η 𝒮) (h_wrong : η ≠ -1)
    (n : ℕ) (hn : 1 ≤ n) (α : Fin n → Fin 2 ⊕ Fin 2)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    P.W n α f = 0 := by
  by_contra h_ne
  exact h_wrong (dirac_os_spin_statistics_any_nPoint_unconditional P ⟨n, hn, α, f, h_ne⟩)

lemma sum_ite_two (a₀ a₁ : ι) (G : ι → ι → ℂ) :
    (∑ x₀ : ι, ∑ x₁ : ι, if x₀ = a₀ then if x₁ = a₁ then G x₀ x₁ else 0 else 0) = G a₀ a₁ := by
  have h1 : ∀ x₀ : ι,
      (∑ x₁ : ι, if x₀ = a₀ then if x₁ = a₁ then G x₀ x₁ else 0 else 0) =
      if x₀ = a₀ then G x₀ a₁ else 0 := by
    intro x₀
    by_cases hx₀ : x₀ = a₀ <;> simp [hx₀]
  simp_rw [h1]
  simp

lemma sum_tensorProdRep_left_two {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁]
    [Fintype ι₂] [DecidableEq ι₂]
    (R₁ : HolomorphicLorentzRep ι₁) (R₂ : HolomorphicLorentzRep ι₂)
    (A : SL2C) (hR₂ : R₂.σ (A, 1) = 1)
    (F : (Fin 2 → ι₁ × ι₂) → ℂ) (α₁ : Fin 2 → ι₁) (α₂ : Fin 2 → ι₂) :
    (∑ β : Fin 2 → ι₁ × ι₂,
      (∏ i : Fin 2, (tensorProdRep R₁ R₂).σ (A, 1) (α₁ i, α₂ i) (β i)) * F β) =
    ∑ β₁ : Fin 2 → ι₁,
      (∏ i : Fin 2, R₁.σ (A, 1) (α₁ i) (β₁ i)) * F (fun i => (β₁ i, α₂ i)) := by
  rw [sum_fin_two_fun (ι := ι₁ × ι₂), sum_fin_two_fun (ι := ι₁)]
  simp only [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun b₀ _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b₁ _ => ?_)
  let c : ℂ := R₁.σ (A, 1) (α₁ 0) b₀ * R₁.σ (A, 1) (α₁ 1) b₁
  have h_prod : ∀ r₀ r₁ : ι₂,
      (∏ i : Fin 2, (tensorProdRep R₁ R₂).σ (A, 1) (α₁ i, α₂ i) (![(b₀, r₀), (b₁, r₁)] i)) *
        F ![(b₀, r₀), (b₁, r₁)] =
      if r₀ = α₂ 0 then
        if r₁ = α₂ 1 then
          c * F ![(b₀, r₀), (b₁, r₁)]
        else 0
      else 0 := by
    intro r₀ r₁
    rw [Fin.prod_univ_two]
    change (R₁.σ (A, 1) (α₁ 0) b₀ * R₂.σ (A, 1) (α₂ 0) r₀) *
        (R₁.σ (A, 1) (α₁ 1) b₁ * R₂.σ (A, 1) (α₂ 1) r₁) * F ![(b₀, r₀), (b₁, r₁)] = _
    rw [hR₂]
    by_cases h0 : r₀ = α₂ 0
    · subst h0
      by_cases h1 : r₁ = α₂ 1
      · subst h1
        simp [c]
      · have hne : α₂ 1 ≠ r₁ := Ne.symm h1
        simp [h1, Matrix.one_apply_ne hne]
    · have hne : α₂ 0 ≠ r₀ := Ne.symm h0
      simp [h0, Matrix.one_apply_ne hne]
  simp_rw [h_prod]
  refine (sum_ite_two (α₂ 0) (α₂ 1) (fun r₀ r₁ => c * F ![(b₀, r₀), (b₁, r₁)])).trans ?_
  rw [Fin.prod_univ_two]
  have h_arg : (![(b₀, α₂ 0), (b₁, α₂ 1)] : Fin 2 → ι₁ × ι₂) =
      fun i => (![b₀, b₁] i, α₂ i) := by
    ext i <;> fin_cases i <;> rfl
  rw [h_arg]
  rfl

lemma sum_tensorProdRep_right_two {ι₁ ι₂ : Type*} [Fintype ι₁] [DecidableEq ι₁]
    [Fintype ι₂] [DecidableEq ι₂]
    (R₁ : HolomorphicLorentzRep ι₁) (R₂ : HolomorphicLorentzRep ι₂)
    (B : SL2C) (hR₁ : R₁.σ (1, B) = 1)
    (F : (Fin 2 → ι₁ × ι₂) → ℂ) (α₁ : Fin 2 → ι₁) (α₂ : Fin 2 → ι₂) :
    (∑ β : Fin 2 → ι₁ × ι₂,
      (∏ i : Fin 2, (tensorProdRep R₁ R₂).σ (1, B) (α₁ i, α₂ i) (β i)) * F β) =
    ∑ β₂ : Fin 2 → ι₂,
      (∏ i : Fin 2, R₂.σ (1, B) (α₂ i) (β₂ i)) * F (fun i => (α₁ i, β₂ i)) := by
  rw [sum_fin_two_fun (ι := ι₁ × ι₂), sum_fin_two_fun (ι := ι₂)]
  simp only [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b₀ _ => ?_)
  have h_swap : ∀ l₀ : ι₁,
      (∑ l₁ : ι₁, ∑ b₁ : ι₂,
        (∏ i : Fin 2, (tensorProdRep R₁ R₂).σ (1, B) (α₁ i, α₂ i) (![(l₀, b₀), (l₁, b₁)] i)) *
          F ![(l₀, b₀), (l₁, b₁)]) =
      ∑ b₁ : ι₂, ∑ l₁ : ι₁,
        (∏ i : Fin 2, (tensorProdRep R₁ R₂).σ (1, B) (α₁ i, α₂ i) (![(l₀, b₀), (l₁, b₁)] i)) *
          F ![(l₀, b₀), (l₁, b₁)] :=
    fun _ => Finset.sum_comm
  simp_rw [h_swap]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b₁ _ => ?_)
  let c : ℂ := R₂.σ (1, B) (α₂ 0) b₀ * R₂.σ (1, B) (α₂ 1) b₁
  have h_prod : ∀ l₀ l₁ : ι₁,
      (∏ i : Fin 2, (tensorProdRep R₁ R₂).σ (1, B) (α₁ i, α₂ i) (![(l₀, b₀), (l₁, b₁)] i)) *
        F ![(l₀, b₀), (l₁, b₁)] =
      if l₀ = α₁ 0 then
        if l₁ = α₁ 1 then
          c * F ![(l₀, b₀), (l₁, b₁)]
        else 0
      else 0 := by
    intro l₀ l₁
    rw [Fin.prod_univ_two]
    change (R₁.σ (1, B) (α₁ 0) l₀ * R₂.σ (1, B) (α₂ 0) b₀) *
        (R₁.σ (1, B) (α₁ 1) l₁ * R₂.σ (1, B) (α₂ 1) b₁) * F ![(l₀, b₀), (l₁, b₁)] = _
    rw [hR₁]
    by_cases h0 : l₀ = α₁ 0
    · subst h0
      by_cases h1 : l₁ = α₁ 1
      · subst h1
        simp [c]
      · have hne : α₁ 1 ≠ l₁ := Ne.symm h1
        simp [h1, Matrix.one_apply_ne hne]
    · have hne : α₁ 0 ≠ l₀ := Ne.symm h0
      simp [h0, Matrix.one_apply_ne hne]
  simp_rw [h_prod]
  refine (sum_ite_two (α₁ 0) (α₁ 1) (fun l₀ l₁ => c * F ![(l₀, b₀), (l₁, b₁)])).trans ?_
  rw [Fin.prod_univ_two]
  have h_arg : (![(α₁ 0, b₀), (α₁ 1, b₁)] : Fin 2 → ι₁ × ι₂) =
      fun i => (α₁ i, ![b₀, b₁] i) := by
    ext i <;> fin_cases i <;> rfl
  rw [h_arg]
  rfl

theorem vladimirov_H_zero_twoPointIndexExchange_tensorProd_weyl
    (W : WightmanFamily (Fin 2 × Fin 2))
    (hspec : SpectrumCondition W)
    (hP : PoincareCovariant (tensorProdRep leftWeylRep rightWeylRep) W)
    (α : Fin 2 → Fin 2 × Fin 2) :
    vladimirov_H W 2 α 0 = (1 : ℂ) * vladimirov_H W 2 (α ∘ Fin.rev) 0 := by
  have h_left : ∀ (α₂ : Fin 2 → Fin 2) (α₁ : Fin 2 → Fin 2),
      vladimirov_H W 2 (fun i => (α₁ i, α₂ i)) 0 =
        (-1 : ℂ) * vladimirov_H W 2 (fun i => (α₁ (Fin.rev i), α₂ i)) 0 := by
    intro α₂
    refine finTwo_antisymm_of_diagImag_symplectic
      (fun α₁ => vladimirov_H W 2 (fun i => (α₁ i, α₂ i)) 0)
      (fun α₁ => ?_) (fun α₁ => ?_)
    · have h := vladimirov_H_zero_complexCovariant
        (tensorProdRep leftWeylRep rightWeylRep) W hspec hP 2 diagImagSL2C 1
        (fun i => (α₁ i, α₂ i))
      rw [h]
      exact sum_tensorProdRep_left_two leftWeylRep rightWeylRep diagImagSL2C rfl
        (fun β => vladimirov_H W 2 β 0) α₁ α₂
    · have h := vladimirov_H_zero_complexCovariant
        (tensorProdRep leftWeylRep rightWeylRep) W hspec hP 2 symplecticSL2C 1
        (fun i => (α₁ i, α₂ i))
      rw [h]
      exact sum_tensorProdRep_left_two leftWeylRep rightWeylRep symplecticSL2C rfl
        (fun β => vladimirov_H W 2 β 0) α₁ α₂
  have h_right : ∀ (α₁ : Fin 2 → Fin 2) (α₂ : Fin 2 → Fin 2),
      vladimirov_H W 2 (fun i => (α₁ i, α₂ i)) 0 =
        (-1 : ℂ) * vladimirov_H W 2 (fun i => (α₁ i, α₂ (Fin.rev i))) 0 := by
    intro α₁
    refine finTwo_antisymm_of_diagImag_symplectic
      (fun α₂ => vladimirov_H W 2 (fun i => (α₁ i, α₂ i)) 0)
      (fun α₂ => ?_) (fun α₂ => ?_)
    · have h := vladimirov_H_zero_complexCovariant
        (tensorProdRep leftWeylRep rightWeylRep) W hspec hP 2 1 diagImagSL2C
        (fun i => (α₁ i, α₂ i))
      rw [h]
      exact sum_tensorProdRep_right_two leftWeylRep rightWeylRep diagImagSL2C rfl
        (fun β => vladimirov_H W 2 β 0) α₁ α₂
    · have h := vladimirov_H_zero_complexCovariant
        (tensorProdRep leftWeylRep rightWeylRep) W hspec hP 2 1 symplecticSL2C
        (fun i => (α₁ i, α₂ i))
      rw [h]
      exact sum_tensorProdRep_right_two leftWeylRep rightWeylRep symplecticSL2C rfl
        (fun β => vladimirov_H W 2 β 0) α₁ α₂
  have hα : α = fun i => ((α i).1, (α i).2) := rfl
  have h1 := h_left (fun i => (α i).2) (fun i => (α i).1)
  have h2 := h_right (fun i => (α (Fin.rev i)).1) (fun i => (α i).2)
  rw [hα, h1, h2]
  have h_rev : (fun i : Fin 2 => ((α (Fin.rev i)).1, (α (Fin.rev i)).2)) = α ∘ Fin.rev := rfl
  rw [h_rev]
  ring

theorem fourVectorSpinor_wightman_spin_statistics_unconditional
    (W : WightmanFamily (Fin 2 × Fin 2))
    (hspec : SpectrumCondition W)
    (hP : PoincareCovariant (tensorProdRep leftWeylRep rightWeylRep) W)
    {η : ℂ} (hloc : WeakLocality η W)
    (h_nondeg : ∃ (α : Fin 2 → Fin 2 × Fin 2) (f : SchwartzMap (Fin 2 → Fin 4 → ℝ) ℂ),
      W 2 α f ≠ 0) :
    η = 1 :=
  spin_statistics_of_vladimirov_H_zero_twoPointIndexExchange hspec hloc
    (vladimirov_H_zero_twoPointIndexExchange_tensorProd_weyl W hspec hP) h_nondeg

theorem fourVectorSpinor_os_spin_statistics_any_nPoint_unconditional
    {S : StarStructure (tensorProdRep leftWeylRep rightWeylRep)}
    {η : ℂ} {𝒮 : SchwingerFamily (Fin 2 × Fin 2)}
    (P : OSReconstructedWightman (tensorProdRep leftWeylRep rightWeylRep) S η 𝒮)
    (h_nondeg : ∃ (n : ℕ) (_ : 1 ≤ n) (α : Fin n → Fin 2 × Fin 2)
      (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ), P.W n α f ≠ 0) :
    η = 1 := by
  by_contra h_wrong
  rcases h_nondeg with ⟨n, hn, α, f, hf⟩
  have h2_zero : ∀ (β : Fin 2 → Fin 2 × Fin 2) (g : SchwartzMap (Fin 2 → Fin 4 → ℝ) ℂ),
      P.W 2 β g = 0 :=
    wightman_twoPoint_eq_zero_of_vladimirov_H_zero_twoPointIndexExchange
      P.spectrum P.weakLocality
      (vladimirov_H_zero_twoPointIndexExchange_tensorProd_weyl P.W P.spectrum P.poincare)
      h_wrong
  exact hf (wightman_eq_zero_of_twoPoint_eq_zero_of_positivity
    S P.W P.spectrum P.positivity h2_zero n hn α f)

theorem OSAxioms.twoPoint_eq_eta_mul_rev
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {η : ℂ} {𝒮 : SchwingerFamily ι}
    (hOS : OSAxioms R S η 𝒮)
    (α : Fin 2 → ι) {x : Fin 2 → Fin 4 → ℝ} (hx : x ∈ orderedEuclidN 2) :
    𝒮 2 α x = η * 𝒮 2 (α ∘ Fin.rev) x := by
  rw [← osTranslationInvariant_neg_rev_two hOS.os1_translation α x hx]
  have h := hOS.os3_symmetry 2 α x hx
  rwa [two_mul_two_sub_one_div_two, pow_one] at h

lemma osKernel_onePoint_chiralDoubleStarStructure_inl
    {R : HolomorphicLorentzRep ι} (hR : R.HasRealConj)
    (𝒮 : SchwingerFamily (ι ⊕ ι)) (c : ι) (y : posOrderedEuclidN 1) :
    osKernel (chiralDoubleStarStructure R hR) 𝒮
      ⟨1, (fun _ => Sum.inl c, y)⟩ ⟨1, (fun _ => Sum.inl c, y)⟩ =
      𝒮 2 ![Sum.inr c, Sum.inl c] (osConcatPoint 1 1 y.val y.val) := by
  unfold osKernel
  dsimp only
  have h_term : ∀ β : Fin 1 → ι ⊕ ι,
      (∏ i : Fin 1, (chiralDoubleStarStructure R hR).C (Sum.inl c) (β i)) *
        𝒮 (1 + 1) (osConcatIdx 1 1 β (fun _ => Sum.inl c))
          (osConcatPoint 1 1 y.val y.val) =
      if β = (fun _ => Sum.inr c) then
        𝒮 2 ![Sum.inr c, Sum.inl c] (osConcatPoint 1 1 y.val y.val)
      else 0 := by
    intro β
    rw [Fin.prod_univ_one]
    by_cases hβ : β = fun _ => Sum.inr c
    · subst hβ
      simp only [↓reduceIte, chiralDoubleStarStructure, Matrix.fromBlocks_apply₁₂,
        Matrix.one_apply_eq, one_mul]
      congr 1
      ext i
      fin_cases i <;> rfl
    · rw [if_neg hβ]
      have hβ0 : β 0 ≠ Sum.inr c := by
        intro hc
        apply hβ
        ext i
        rw [Subsingleton.elim i 0, hc]
      have hC : (chiralDoubleStarStructure R hR).C (Sum.inl c) (β 0) = 0 := by
        rcases h0 : β 0 with a | a
        · rfl
        · change (1 : Matrix ι ι ℂ) c a = 0
          refine Matrix.one_apply_ne (fun hca => hβ0 ?_)
          rw [h0, hca]
      rw [hC, zero_mul]
  simp_rw [h_term]
  rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]

lemma osKernel_onePoint_chiralDoubleStarStructure_inr
    {R : HolomorphicLorentzRep ι} (hR : R.HasRealConj)
    (𝒮 : SchwingerFamily (ι ⊕ ι)) (c : ι) (y : posOrderedEuclidN 1) :
    osKernel (chiralDoubleStarStructure R hR) 𝒮
      ⟨1, (fun _ => Sum.inr c, y)⟩ ⟨1, (fun _ => Sum.inr c, y)⟩ =
      𝒮 2 ![Sum.inl c, Sum.inr c] (osConcatPoint 1 1 y.val y.val) := by
  unfold osKernel
  dsimp only
  have h_term : ∀ β : Fin 1 → ι ⊕ ι,
      (∏ i : Fin 1, (chiralDoubleStarStructure R hR).C (Sum.inr c) (β i)) *
        𝒮 (1 + 1) (osConcatIdx 1 1 β (fun _ => Sum.inr c))
          (osConcatPoint 1 1 y.val y.val) =
      if β = (fun _ => Sum.inl c) then
        𝒮 2 ![Sum.inl c, Sum.inr c] (osConcatPoint 1 1 y.val y.val)
      else 0 := by
    intro β
    rw [Fin.prod_univ_one]
    by_cases hβ : β = fun _ => Sum.inl c
    · subst hβ
      simp only [↓reduceIte, chiralDoubleStarStructure, Matrix.fromBlocks_apply₂₁,
        Matrix.one_apply_eq, one_mul]
      congr 1
      ext i
      fin_cases i <;> rfl
    · rw [if_neg hβ]
      have hβ0 : β 0 ≠ Sum.inl c := by
        intro hc
        apply hβ
        ext i
        rw [Subsingleton.elim i 0, hc]
      have hC : (chiralDoubleStarStructure R hR).C (Sum.inr c) (β 0) = 0 := by
        rcases h0 : β 0 with a | a
        · change (1 : Matrix ι ι ℂ) c a = 0
          refine Matrix.one_apply_ne (fun hca => hβ0 ?_)
          rw [h0, hca]
        · rfl
      rw [hC, zero_mul]
  simp_rw [h_term]
  rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]

lemma osKernel_self_re_nonneg_and_eq_ofReal
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (A : OSConfig ι) :
    0 ≤ (osKernel S D.𝒮 A A).re ∧ osKernel S D.𝒮 A A = ((osKernel S D.𝒮 A A).re : ℂ) := by
  have h_pos := D.positivity (Finsupp.single A 1)
  have h_single : osPreInner S D.𝒮 (Finsupp.single A 1) (Finsupp.single A 1) =
      osKernel S D.𝒮 A A := by
    unfold osPreInner
    simp
  rw [h_single] at h_pos
  have h_symm := osKernel_conj_symm S D.𝒮 D.hermiticity A A
  refine ⟨h_pos, ?_⟩
  exact (Complex.conj_eq_iff_re.mp h_symm).symm

theorem osKernel_onePoint_eq_zero_of_chiralDoubleStarStructure_of_eta_ne_one
    {R : HolomorphicLorentzRep ι} (hR : R.HasRealConj)
    {η : ℂ} {𝒮 : SchwingerFamily (ι ⊕ ι)}
    (hOS : OSAxioms (directSumRep R (chiralSwapRep R)) (chiralDoubleStarStructure R hR) η 𝒮)
    (hη : η ≠ 1) (γ : ι ⊕ ι) (y : posOrderedEuclidN 1) :
    osKernel (chiralDoubleStarStructure R hR) 𝒮 ⟨1, (fun _ => γ, y)⟩ ⟨1, (fun _ => γ, y)⟩ = 0 := by
  have h_pair : ∀ c : ι,
      osKernel (chiralDoubleStarStructure R hR) 𝒮
        ⟨1, (fun _ => Sum.inl c, y)⟩ ⟨1, (fun _ => Sum.inl c, y)⟩ = 0 ∧
      osKernel (chiralDoubleStarStructure R hR) 𝒮
        ⟨1, (fun _ => Sum.inr c, y)⟩ ⟨1, (fun _ => Sum.inr c, y)⟩ = 0 := by
    intro c
    set u := osKernel (chiralDoubleStarStructure R hR) 𝒮
      ⟨1, (fun _ => Sum.inl c, y)⟩ ⟨1, (fun _ => Sum.inl c, y)⟩
    set v := osKernel (chiralDoubleStarStructure R hR) 𝒮
      ⟨1, (fun _ => Sum.inr c, y)⟩ ⟨1, (fun _ => Sum.inr c, y)⟩
    have hu := osKernel_self_re_nonneg_and_eq_ofReal hOS.toReflectionPositiveData
      ⟨1, (fun _ => Sum.inl c, y)⟩
    have hv := osKernel_self_re_nonneg_and_eq_ofReal hOS.toReflectionPositiveData
      ⟨1, (fun _ => Sum.inr c, y)⟩
    change 0 ≤ u.re ∧ u = (u.re : ℂ) at hu
    change 0 ≤ v.re ∧ v = (v.re : ℂ) at hv
    have h_ord : osConcatPoint 1 1 y.val y.val ∈ orderedEuclidN 2 :=
      osConcatPoint_mem_orderedEuclidN 1 1 y.property y.property
    have huv : u = η * v := by
      change osKernel (chiralDoubleStarStructure R hR) 𝒮
        ⟨1, (fun _ => Sum.inl c, y)⟩ ⟨1, (fun _ => Sum.inl c, y)⟩ =
        η * osKernel (chiralDoubleStarStructure R hR) 𝒮
          ⟨1, (fun _ => Sum.inr c, y)⟩ ⟨1, (fun _ => Sum.inr c, y)⟩
      rw [osKernel_onePoint_chiralDoubleStarStructure_inl,
          osKernel_onePoint_chiralDoubleStarStructure_inr]
      have h_rev : (![Sum.inr c, Sum.inl c] : Fin 2 → ι ⊕ ι) ∘ Fin.rev =
          ![Sum.inl c, Sum.inr c] := finTwo_comp_rev_vecCons (Sum.inr c) (Sum.inl c)
      rw [← h_rev]
      exact hOS.twoPoint_eq_eta_mul_rev ![Sum.inr c, Sum.inl c] h_ord
    have hvu : v = η * u := by
      change osKernel (chiralDoubleStarStructure R hR) 𝒮
        ⟨1, (fun _ => Sum.inr c, y)⟩ ⟨1, (fun _ => Sum.inr c, y)⟩ =
        η * osKernel (chiralDoubleStarStructure R hR) 𝒮
          ⟨1, (fun _ => Sum.inl c, y)⟩ ⟨1, (fun _ => Sum.inl c, y)⟩
      rw [osKernel_onePoint_chiralDoubleStarStructure_inr,
          osKernel_onePoint_chiralDoubleStarStructure_inl]
      have h_rev : (![Sum.inl c, Sum.inr c] : Fin 2 → ι ⊕ ι) ∘ Fin.rev =
          ![Sum.inr c, Sum.inl c] := finTwo_comp_rev_vecCons (Sum.inl c) (Sum.inr c)
      rw [← h_rev]
      exact hOS.twoPoint_eq_eta_mul_rev ![Sum.inl c, Sum.inr c] h_ord
    by_cases hη_neg : η = -1
    · have h_re : u.re = -v.re := by
        rw [huv, hη_neg]
        simp
      have hu_re : u.re = 0 := by linarith [hu.1, hv.1, h_re]
      have hv_re : v.re = 0 := by linarith [hu.1, hv.1, h_re]
      exact ⟨by rw [hu.2, hu_re, Complex.ofReal_zero],
             by rw [hv.2, hv_re, Complex.ofReal_zero]⟩
    · have h_sq : (1 - η ^ 2) * u = 0 := by
        calc (1 - η ^ 2) * u = u - η * (η * u) := by ring
          _ = u - η * v := by rw [← hvu]
          _ = 0 := by rw [← huv, sub_self]
      have h_ne : 1 - η ^ 2 ≠ 0 := by
        intro h0
        have h_eq : η ^ 2 = 1 := (sub_eq_zero.mp h0).symm
        rcases sq_eq_one_iff.mp h_eq with h1 | h2
        · exact hη h1
        · exact hη_neg h2
      have hu0 : u = 0 := (mul_eq_zero.mp h_sq).resolve_left h_ne
      have hv0 : v = 0 := by rw [hvu, hu0, mul_zero]
      exact ⟨hu0, hv0⟩
  rcases γ with c | c
  · exact (h_pair c).1
  · exact (h_pair c).2

theorem all_nPoint_eq_zero_of_chiralDoubleStarStructure_of_eta_ne_one
    {R : HolomorphicLorentzRep ι} (hR : R.HasRealConj)
    {η : ℂ} {𝒮 : SchwingerFamily (ι ⊕ ι)}
    (P : OSReconstructedWightman (directSumRep R (chiralSwapRep R))
      (chiralDoubleStarStructure R hR) η 𝒮)
    (hη : η ≠ 1) :
    (∀ (n : ℕ), 1 ≤ n → ∀ (α : Fin n → ι ⊕ ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → 𝒮 n α x = 0) ∧
    (∀ (n : ℕ), 1 ≤ n → ∀ (α : Fin n → ι ⊕ ι) (z : Fin n → Fin 4 → ℂ),
      z ∈ forward_tube_n n → P.E.H n α z = 0) ∧
    (∀ (n : ℕ), 1 ≤ n → ∀ (α : Fin n → ι ⊕ ι) (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ),
      P.W n α f = 0) ∧
    (OSVacuumNormalized 𝒮 → ∀ Φ : P.Hilbert, Φ = ⟪P.vacuum, Φ⟫_ℂ • P.vacuum) := by
  have h1 : ∀ (γ : ι ⊕ ι) (y : posOrderedEuclidN 1),
      osKernel (chiralDoubleStarStructure R hR) 𝒮 ⟨1, (fun _ => γ, y)⟩ ⟨1, (fun _ => γ, y)⟩ = 0 :=
    osKernel_onePoint_eq_zero_of_chiralDoubleStarStructure_of_eta_ne_one hR P.osAxioms hη
  have h_schw : ∀ (n : ℕ), 1 ≤ n → ∀ (α : Fin n → ι ⊕ ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → 𝒮 n α x = 0 :=
    fun n hn α x hx =>
      schwinger_eq_zero_of_onePoint_osKernel_eq_zero P.osData P.osAxioms.os1_translation h1
        n hn α hx
  have h2 : ∀ (β : Fin 2 → ι ⊕ ι) (y : Fin 2 → Fin 4 → ℝ),
      y ∈ orderedEuclidN 2 → 𝒮 2 β y = 0 :=
    fun β y hy => h_schw 2 (by omega) β y hy
  exact ⟨h_schw,
    fun n hn α z hz => P.tube_eq_zero_of_twoPoint_eq_zero h2 n hn α z hz,
    fun n hn α f => P.wightman_eq_zero_of_twoPoint_eq_zero h2 n hn α f,
    fun hnorm Φ => eq_smul_osVacuum_of_twoPoint_eq_zero P.osData P.osAxioms.os1_translation
      hnorm h2 Φ⟩

lemma spinorTensorRep_sigma_neg_one_one (m₁ m₂ : ℕ)
    (a b : (Fin m₁ → Fin 2) × (Fin m₂ → Fin 2)) :
    (spinorTensorRep m₁ m₂).σ (-1, 1) a b =
      if b = a then (-1 : ℂ) ^ m₁ else 0 := by
  rcases a with ⟨a₁, a₂⟩
  rcases b with ⟨b₁, b₂⟩
  change (∏ k : Fin m₁, (-1 : SL2C).1 (a₁ k) (b₁ k)) *
      (∏ k : Fin m₂, (1 : SL2C).1 (a₂ k) (b₂ k)) =
    if (b₁, b₂) = (a₁, a₂) then (-1 : ℂ) ^ m₁ else 0
  have h1 : (∏ k : Fin m₁, (-1 : SL2C).1 (a₁ k) (b₁ k)) =
      if b₁ = a₁ then (-1 : ℂ) ^ m₁ else 0 := by
    by_cases h : b₁ = a₁
    · subst h
      simp [Finset.prod_const]
    · rw [if_neg h]
      obtain ⟨k, hk⟩ : ∃ k, a₁ k ≠ b₁ k := by
        by_contra hc
        push Not at hc
        exact h (funext hc).symm
      refine Finset.prod_eq_zero (Finset.mem_univ k) ?_
      change -((1 : Matrix (Fin 2) (Fin 2) ℂ) (a₁ k) (b₁ k)) = 0
      rw [Matrix.one_apply_ne hk, neg_zero]
  have h2 : (∏ k : Fin m₂, (1 : SL2C).1 (a₂ k) (b₂ k)) =
      if b₂ = a₂ then 1 else 0 := by
    by_cases h : b₂ = a₂
    · subst h
      simp
    · rw [if_neg h]
      obtain ⟨k, hk⟩ : ∃ k, a₂ k ≠ b₂ k := by
        by_contra hc
        push Not at hc
        exact h (funext hc).symm
      refine Finset.prod_eq_zero (Finset.mem_univ k) ?_
      exact Matrix.one_apply_ne hk
  rw [h1, h2]
  by_cases h₁ : b₁ = a₁ <;> by_cases h₂ : b₂ = a₂ <;> simp [h₁, h₂, Prod.ext_iff]

lemma chiralSwap_spinorTensorRep_sigma_neg_one_one (m₁ m₂ : ℕ)
    (a b : (Fin m₁ → Fin 2) × (Fin m₂ → Fin 2)) :
    (chiralSwapRep (spinorTensorRep m₁ m₂)).σ (-1, 1) a b =
      if b = a then (-1 : ℂ) ^ m₂ else 0 := by
  rcases a with ⟨a₁, a₂⟩
  rcases b with ⟨b₁, b₂⟩
  change (∏ k : Fin m₁, (1 : SL2C).1 (a₁ k) (b₁ k)) *
      (∏ k : Fin m₂, (-1 : SL2C).1 (a₂ k) (b₂ k)) =
    if (b₁, b₂) = (a₁, a₂) then (-1 : ℂ) ^ m₂ else 0
  have h1 : (∏ k : Fin m₁, (1 : SL2C).1 (a₁ k) (b₁ k)) =
      if b₁ = a₁ then 1 else 0 := by
    by_cases h : b₁ = a₁
    · subst h; simp
    · rw [if_neg h]
      obtain ⟨k, hk⟩ : ∃ k, a₁ k ≠ b₁ k := by
        by_contra hc; push Not at hc; exact h (funext hc).symm
      exact Finset.prod_eq_zero (Finset.mem_univ k) (Matrix.one_apply_ne hk)
  have h2 : (∏ k : Fin m₂, (-1 : SL2C).1 (a₂ k) (b₂ k)) =
      if b₂ = a₂ then (-1 : ℂ) ^ m₂ else 0 := by
    by_cases h : b₂ = a₂
    · subst h; simp [Finset.prod_const]
    · rw [if_neg h]
      obtain ⟨k, hk⟩ : ∃ k, a₂ k ≠ b₂ k := by
        by_contra hc; push Not at hc; exact h (funext hc).symm
      refine Finset.prod_eq_zero (Finset.mem_univ k) ?_
      change -((1 : Matrix (Fin 2) (Fin 2) ℂ) (a₂ k) (b₂ k)) = 0
      rw [Matrix.one_apply_ne hk, neg_zero]
  rw [h1, h2]
  by_cases h₁ : b₁ = a₁ <;> by_cases h₂ : b₂ = a₂ <;> simp [h₁, h₂, Prod.ext_iff]

theorem vladimirov_H_zero_spinorTensorBispinor_mixed_eq_zero_of_odd
    (m₁ m₂ : ℕ) (hm : Odd (m₁ + m₂))
    (W : WightmanFamily (((Fin m₁ → Fin 2) × (Fin m₂ → Fin 2)) ⊕
      ((Fin m₁ → Fin 2) × (Fin m₂ → Fin 2))))
    (hspec : SpectrumCondition W)
    (hP : PoincareCovariant
      (directSumRep (spinorTensorRep m₁ m₂) (chiralSwapRep (spinorTensorRep m₁ m₂))) W)
    (a b : (Fin m₁ → Fin 2) × (Fin m₂ → Fin 2)) :
    vladimirov_H W 2 ![Sum.inl a, Sum.inr b] 0 = 0 ∧
    vladimirov_H W 2 ![Sum.inr a, Sum.inl b] 0 = 0 := by
  let R := directSumRep (spinorTensorRep m₁ m₂) (chiralSwapRep (spinorTensorRep m₁ m₂))
  have h_pow : (-1 : ℂ) ^ m₁ * (-1 : ℂ) ^ m₂ = -1 := by
    rw [← pow_add]
    exact Odd.neg_one_pow hm
  have h_pow' : (-1 : ℂ) ^ m₂ * (-1 : ℂ) ^ m₁ = -1 := by
    rw [mul_comm, h_pow]
  constructor
  · have h_cov := vladimirov_H_zero_complexCovariant R W hspec hP 2 (-1) 1
      ![Sum.inl a, Sum.inr b]
    have h_prod : ∀ β : Fin 2 → ((Fin m₁ → Fin 2) × (Fin m₂ → Fin 2)) ⊕
        ((Fin m₁ → Fin 2) × (Fin m₂ → Fin 2)),
        (∏ i : Fin 2, R.σ (-1, 1) (![Sum.inl a, Sum.inr b] i) (β i)) =
          if β = ![Sum.inl a, Sum.inr b] then -1 else 0 := by
      intro β
      rw [Fin.prod_univ_two]
      simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
      have h0 : R.σ (-1, 1) (Sum.inl a) (β 0) =
          if β 0 = Sum.inl a then (-1 : ℂ) ^ m₁ else 0 := by
        rcases hβ0 : β 0 with x | x
        · change (spinorTensorRep m₁ m₂).σ (-1, 1) a x =
            if Sum.inl x = Sum.inl a then (-1 : ℂ) ^ m₁ else 0
          rw [spinorTensorRep_sigma_neg_one_one]
          by_cases hax : x = a <;> simp [hax]
        · simp [R, directSumRep]
      have h1 : R.σ (-1, 1) (Sum.inr b) (β 1) =
          if β 1 = Sum.inr b then (-1 : ℂ) ^ m₂ else 0 := by
        rcases hβ1 : β 1 with y | y
        · simp [R, directSumRep]
        · change (chiralSwapRep (spinorTensorRep m₁ m₂)).σ (-1, 1) b y =
            if Sum.inr y = Sum.inr b then (-1 : ℂ) ^ m₂ else 0
          rw [chiralSwap_spinorTensorRep_sigma_neg_one_one]
          by_cases hby : y = b <;> simp [hby]
      rw [h0, h1]
      by_cases hβ : β = ![Sum.inl a, Sum.inr b]
      · subst hβ; simp [h_pow]
      · rw [if_neg hβ]
        by_cases h0' : β 0 = Sum.inl a
        · have h1' : β 1 ≠ Sum.inr b := by
            intro hc; apply hβ; rw [finTwo_eq_vecCons β, h0', hc]
          simp [h0', h1']
        · simp [h0']
    simp_rw [h_prod, ite_mul, neg_one_mul, zero_mul] at h_cov
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _)] at h_cov
    linear_combination (1 / 2 : ℂ) * h_cov
  · have h_cov := vladimirov_H_zero_complexCovariant R W hspec hP 2 (-1) 1
      ![Sum.inr a, Sum.inl b]
    have h_prod : ∀ β : Fin 2 → ((Fin m₁ → Fin 2) × (Fin m₂ → Fin 2)) ⊕
        ((Fin m₁ → Fin 2) × (Fin m₂ → Fin 2)),
        (∏ i : Fin 2, R.σ (-1, 1) (![Sum.inr a, Sum.inl b] i) (β i)) =
          if β = ![Sum.inr a, Sum.inl b] then -1 else 0 := by
      intro β
      rw [Fin.prod_univ_two]
      simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
      have h0 : R.σ (-1, 1) (Sum.inr a) (β 0) =
          if β 0 = Sum.inr a then (-1 : ℂ) ^ m₂ else 0 := by
        rcases hβ0 : β 0 with x | x
        · simp [R, directSumRep]
        · change (chiralSwapRep (spinorTensorRep m₁ m₂)).σ (-1, 1) a x =
            if Sum.inr x = Sum.inr a then (-1 : ℂ) ^ m₂ else 0
          rw [chiralSwap_spinorTensorRep_sigma_neg_one_one]
          by_cases hax : x = a <;> simp [hax]
      have h1 : R.σ (-1, 1) (Sum.inl b) (β 1) =
          if β 1 = Sum.inl b then (-1 : ℂ) ^ m₁ else 0 := by
        rcases hβ1 : β 1 with y | y
        · change (spinorTensorRep m₁ m₂).σ (-1, 1) b y =
            if Sum.inl y = Sum.inl b then (-1 : ℂ) ^ m₁ else 0
          rw [spinorTensorRep_sigma_neg_one_one]
          by_cases hby : y = b <;> simp [hby]
        · simp [R, directSumRep]
      rw [h0, h1]
      by_cases hβ : β = ![Sum.inr a, Sum.inl b]
      · subst hβ; simp [h_pow']
      · rw [if_neg hβ]
        by_cases h0' : β 0 = Sum.inr a
        · have h1' : β 1 ≠ Sum.inl b := by
            intro hc; apply hβ; rw [finTwo_eq_vecCons β, h0', hc]
          simp [h0', h1']
        · simp [h0']
    simp_rw [h_prod, ite_mul, neg_one_mul, zero_mul] at h_cov
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _)] at h_cov
    linear_combination (1 / 2 : ℂ) * h_cov

lemma vladimirovKernel_onePoint_chiralDoubleStarStructure
    {R : HolomorphicLorentzRep ι} (hR : R.HasRealConj)
    {W : WightmanFamily (ι ⊕ ι)} (hspec : SpectrumCondition W) (c : ι) :
    vladimirovKernel (chiralDoubleStarStructure R hR) W 1 1
      (fun _ => Sum.inl c) (fun _ => Sum.inl c) =
      vladimirov_H W 2 ![Sum.inr c, Sum.inl c] 0 ∧
    vladimirovKernel (chiralDoubleStarStructure R hR) W 1 1
      (fun _ => Sum.inr c) (fun _ => Sum.inr c) =
      vladimirov_H W 2 ![Sum.inl c, Sum.inr c] 0 := by
  let y0 : posOrderedEuclidN 1 :=
    ⟨euclidOrderedBasePoint 1, euclidOrderedBasePoint_mem_posOrderedEuclidN 1⟩
  let A_inl : OSConfig (ι ⊕ ι) := ⟨1, (fun _ => Sum.inl c, y0)⟩
  let A_inr : OSConfig (ι ⊕ ι) := ⟨1, (fun _ => Sum.inr c, y0)⟩
  constructor
  · have h_kern := (osKernel_vladimirovSchwinger (chiralDoubleStarStructure R hR)
      hspec A_inl A_inl).symm
    have h_inl := osKernel_onePoint_chiralDoubleStarStructure_inl hR
      (vladimirovSchwinger W) c y0
    exact h_kern.trans (h_inl.trans (vladimirovSchwinger_eq_zero_eval hspec 2 _ _))
  · have h_kern := (osKernel_vladimirovSchwinger (chiralDoubleStarStructure R hR)
      hspec A_inr A_inr).symm
    have h_inr := osKernel_onePoint_chiralDoubleStarStructure_inr hR
      (vladimirovSchwinger W) c y0
    exact h_kern.trans (h_inr.trans (vladimirovSchwinger_eq_zero_eval hspec 2 _ _))

theorem spinorTensorBispinor_os_spin_statistics_any_nPoint_unconditional
    (m₁ m₂ : ℕ) {η : ℂ}
    {𝒮 : SchwingerFamily (((Fin m₁ → Fin 2) × (Fin m₂ → Fin 2)) ⊕
      ((Fin m₁ → Fin 2) × (Fin m₂ → Fin 2)))}
    (P : SpinorTensorBispinorOSReconstructedWightman m₁ m₂ η 𝒮)
    (h_nondeg : ∃ (n : ℕ) (_ : 1 ≤ n)
      (α : Fin n → ((Fin m₁ → Fin 2) × (Fin m₂ → Fin 2)) ⊕
        ((Fin m₁ → Fin 2) × (Fin m₂ → Fin 2)))
      (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ), P.W n α f ≠ 0) :
    η = (-1 : ℂ) ^ (m₁ + m₂) := by
  rcases Nat.even_or_odd (m₁ + m₂) with heven | hodd
  · rw [Even.neg_one_pow heven]
    by_contra hη
    rcases h_nondeg with ⟨n, hn, α, f, hf⟩
    exact hf ((all_nPoint_eq_zero_of_chiralDoubleStarStructure_of_eta_ne_one
      (spinorTensorRep_hasRealConj m₁ m₂) P hη).2.2.1 n hn α f)
  · exfalso
    rcases h_nondeg with ⟨n, hn, α, f, hf⟩
    refine hf (wightman_eq_zero_of_onePoint_vladimirovKernel_eq_zero
      (spinorTensorBispinorStarStructure m₁ m₂) P.W P.spectrum P.positivity (fun γ => ?_) n hn α f)
    unfold spinorTensorBispinorStarStructure
    rcases γ with c | c
    · rw [(vladimirovKernel_onePoint_chiralDoubleStarStructure
          (spinorTensorRep_hasRealConj m₁ m₂) P.spectrum c).1]
      exact (vladimirov_H_zero_spinorTensorBispinor_mixed_eq_zero_of_odd
        m₁ m₂ hodd P.W P.spectrum P.poincare c c).2
    · rw [(vladimirovKernel_onePoint_chiralDoubleStarStructure
          (spinorTensorRep_hasRealConj m₁ m₂) P.spectrum c).2]
      exact (vladimirov_H_zero_spinorTensorBispinor_mixed_eq_zero_of_odd
        m₁ m₂ hodd P.W P.spectrum P.poincare c c).1

theorem spinorTensorBispinor_os_spin_statistics_unconditional
    (m₁ m₂ : ℕ) {η : ℂ}
    {𝒮 : SchwingerFamily (((Fin m₁ → Fin 2) × (Fin m₂ → Fin 2)) ⊕
      ((Fin m₁ → Fin 2) × (Fin m₂ → Fin 2)))}
    (P : SpinorTensorBispinorOSReconstructedWightman m₁ m₂ η 𝒮)
    (h_nondeg : ∃ (α : Fin 2 → ((Fin m₁ → Fin 2) × (Fin m₂ → Fin 2)) ⊕
      ((Fin m₁ → Fin 2) × (Fin m₂ → Fin 2)))
      (f : SchwartzMap (Fin 2 → Fin 4 → ℝ) ℂ), P.W 2 α f ≠ 0) :
    η = (-1 : ℂ) ^ (m₁ + m₂) := by
  rcases h_nondeg with ⟨α, f, hf⟩
  exact spinorTensorBispinor_os_spin_statistics_any_nPoint_unconditional m₁ m₂ P
    ⟨2, by omega, α, f, hf⟩

omit [Fintype ι] [DecidableEq ι] in
lemma osConfig_mk_eq {n : ℕ} {α₁ α₂ : Fin n → ι}
    {x₁ x₂ : posOrderedEuclidN n} (hα : α₁ = α₂) (hx : x₁.val = x₂.val) :
    (⟨n, (α₁, x₁)⟩ : OSConfig ι) = ⟨n, (α₂, x₂)⟩ := by
  subst hα
  exact osConfig_mk_eq_of_val_eq hx

lemma osPrependPoint_timeShift (n : ℕ) (x₀ : Fin 4 → ℝ) (x : Fin n → Fin 4 → ℝ) (τ : ℝ) :
    (fun k => osPrependPoint n x₀ x k + euclidTimeVec τ) =
      osPrependPoint n (x₀ + euclidTimeVec τ) x := by
  ext k μ
  refine Fin.cases ?_ (fun i => ?_) k
  · simp [osPrependPoint]
  · simp only [osPrependPoint, Fin.cons_succ, Pi.add_apply]
    have h0 : euclidTimeVec τ 0 = τ := by simp [euclidTimeVec]
    rw [h0, euclidTimeVec_add]
    simp only [Pi.add_apply]
    ring

lemma osPrependPoint_spatialShift (n : ℕ) (x₀ : Fin 4 → ℝ) (x : Fin n → Fin 4 → ℝ)
    (a : Fin 3 → ℝ) :
    (fun k => osPrependPoint n x₀ x k + euclidSpatialVec a) =
      osPrependPoint n (x₀ + euclidSpatialVec a) (fun i => x i + euclidSpatialVec a) := by
  ext k μ
  refine Fin.cases ?_ (fun i => ?_) k
  · simp [osPrependPoint]
  · simp only [osPrependPoint, Fin.cons_succ, Pi.add_apply, euclidSpatialVec_zero_apply, add_zero]
    ring

lemma time_pos_of_add_euclidTimeVec {x₀ : Fin 4 → ℝ} (hx₀ : 0 < x₀ 0) {τ : ℝ} (hτ : 0 ≤ τ) :
    0 < (x₀ + euclidTimeVec τ) 0 := by
  simp only [Pi.add_apply, euclidTimeVec, ↓reduceIte]
  linarith

lemma time_pos_of_add_euclidSpatialVec {x₀ : Fin 4 → ℝ} (hx₀ : 0 < x₀ 0) (a : Fin 3 → ℝ) :
    0 < (x₀ + euclidSpatialVec a) 0 := by
  simpa [euclidSpatialVec] using hx₀

omit [Fintype ι] [DecidableEq ι] in
theorem osConfigTimeShift_osFieldPrependConfig (α₀ : ι) (x₀ : Fin 4 → ℝ) (hx₀ : 0 < x₀ 0)
    (τ : ℝ) (hτ : 0 ≤ τ) (A : OSConfig ι) :
    osConfigTimeShift τ hτ (osFieldPrependConfig α₀ x₀ hx₀ A) =
      osFieldPrependConfig α₀ (x₀ + euclidTimeVec τ)
        (time_pos_of_add_euclidTimeVec hx₀ hτ) A := by
  rcases A with ⟨n, α, x, hx⟩
  dsimp [osConfigTimeShift, osFieldPrependConfig]
  apply osConfig_mk_eq_of_val_eq
  exact osPrependPoint_timeShift n x₀ x τ

omit [Fintype ι] [DecidableEq ι] in
theorem osConfigSpatialShift_osFieldPrependConfig (α₀ : ι) (x₀ : Fin 4 → ℝ) (hx₀ : 0 < x₀ 0)
    (a : Fin 3 → ℝ) (A : OSConfig ι) :
    osConfigSpatialShift a (osFieldPrependConfig α₀ x₀ hx₀ A) =
      osFieldPrependConfig α₀ (x₀ + euclidSpatialVec a)
        (time_pos_of_add_euclidSpatialVec hx₀ a) (osConfigSpatialShift a A) := by
  rcases A with ⟨n, α, x, hx⟩
  dsimp [osConfigSpatialShift, osFieldPrependConfig]
  apply osConfig_mk_eq_of_val_eq
  exact osPrependPoint_spatialShift n x₀ x a

theorem osTimeShiftLM_comp_osFieldPrependLM
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (α₀ : ι) (x₀ : Fin 4 → ℝ) (hx₀ : 0 < x₀ 0)
    (τ : ℝ) (hτ : 0 ≤ τ) :
    (osTimeShiftLM D τ hτ).comp (osFieldPrependLM D α₀ x₀ hx₀) =
      osFieldPrependLM D α₀ (x₀ + euclidTimeVec τ)
        (time_pos_of_add_euclidTimeVec hx₀ hτ) := by
  unfold osTimeShiftLM osFieldPrependLM
  rw [← osLiftConfigMap_comp]
  congr 1
  ext A : 1
  exact osConfigTimeShift_osFieldPrependConfig α₀ x₀ hx₀ τ hτ A

theorem osTimeShiftLM_osFieldPrependLM
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (α₀ : ι) (x₀ : Fin 4 → ℝ) (hx₀ : 0 < x₀ 0)
    (τ : ℝ) (hτ : 0 ≤ τ) (Ψ : OSPreHilbertSpace D) :
    osTimeShiftLM D τ hτ (osFieldPrependLM D α₀ x₀ hx₀ Ψ) =
      osFieldPrependLM D α₀ (x₀ + euclidTimeVec τ)
        (time_pos_of_add_euclidTimeVec hx₀ hτ) Ψ := by
  rw [← LinearMap.comp_apply, osTimeShiftLM_comp_osFieldPrependLM]

theorem osSpatialTranslateLM_comp_osFieldPrependLM
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (α₀ : ι) (x₀ : Fin 4 → ℝ) (hx₀ : 0 < x₀ 0)
    (a : Fin 3 → ℝ) :
    (osSpatialTranslateLM D a).comp (osFieldPrependLM D α₀ x₀ hx₀) =
      (osFieldPrependLM D α₀ (x₀ + euclidSpatialVec a)
        (time_pos_of_add_euclidSpatialVec hx₀ a)).comp (osSpatialTranslateLM D a) := by
  unfold osSpatialTranslateLM osFieldPrependLM
  rw [← osLiftConfigMap_comp, ← osLiftConfigMap_comp]
  congr 1
  ext A : 1
  exact osConfigSpatialShift_osFieldPrependConfig α₀ x₀ hx₀ a A

theorem osSpatialTranslateLM_osFieldPrependLM
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (α₀ : ι) (x₀ : Fin 4 → ℝ) (hx₀ : 0 < x₀ 0)
    (a : Fin 3 → ℝ) (Ψ : OSPreHilbertSpace D) :
    osSpatialTranslateLM D a (osFieldPrependLM D α₀ x₀ hx₀ Ψ) =
      osFieldPrependLM D α₀ (x₀ + euclidSpatialVec a)
        (time_pos_of_add_euclidSpatialVec hx₀ a) (osSpatialTranslateLM D a Ψ) := by
  rw [← LinearMap.comp_apply, osSpatialTranslateLM_comp_osFieldPrependLM, LinearMap.comp_apply]

theorem osContractionSemigroup_toOSHilbert_osFieldPrependLM
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (hcontr : OSContractionCondition D)
    (α₀ : ι) (x₀ : Fin 4 → ℝ) (hx₀ : 0 < x₀ 0)
    (τ : ℝ) (hτ : 0 ≤ τ) (Ψ : OSPreHilbertSpace D) :
    osContractionSemigroup D hcontr τ hτ
      (toOSHilbert D (osFieldPrependLM D α₀ x₀ hx₀ Ψ)) =
      toOSHilbert D (osFieldPrependLM D α₀ (x₀ + euclidTimeVec τ)
        (time_pos_of_add_euclidTimeVec hx₀ hτ) Ψ) := by
  rw [osContractionSemigroup_toOSHilbert, osTimeShiftLM_osFieldPrependLM]

theorem osSpatialTranslate_toOSHilbert_osFieldPrependLM
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (htrans : OSTranslationInvariant D.𝒮)
    (α₀ : ι) (x₀ : Fin 4 → ℝ) (hx₀ : 0 < x₀ 0)
    (a : Fin 3 → ℝ) (Ψ : OSPreHilbertSpace D) :
    osSpatialTranslate D htrans a
      (toOSHilbert D (osFieldPrependLM D α₀ x₀ hx₀ Ψ)) =
      toOSHilbert D (osFieldPrependLM D α₀ (x₀ + euclidSpatialVec a)
        (time_pos_of_add_euclidSpatialVec hx₀ a) (osSpatialTranslateLM D a Ψ)) := by
  rw [osSpatialTranslate_toOSHilbert, osSpatialTranslateLM_osFieldPrependLM]

def osTailPoint (n : ℕ) (x : Fin (n + 1) → Fin 4 → ℝ) : Fin n → Fin 4 → ℝ :=
  fun i => x (Fin.succ i) - euclidTimeVec (x 0 0)

@[simp]
lemma osPrependPoint_osTailPoint (n : ℕ) (x : Fin (n + 1) → Fin 4 → ℝ) :
    osPrependPoint n (x 0) (osTailPoint n x) = x := by
  ext k μ
  refine Fin.cases ?_ (fun i => ?_) k
  · simp [osPrependPoint]
  · simp [osPrependPoint, osTailPoint]

@[simp]
lemma osTailPoint_osPrependPoint (n : ℕ) (x₀ : Fin 4 → ℝ) (x : Fin n → Fin 4 → ℝ) :
    osTailPoint n (osPrependPoint n x₀ x) = x := by
  ext i μ
  simp [osTailPoint, osPrependPoint]

lemma osTailPoint_mem_posOrderedEuclidN (n : ℕ)
    {x : Fin (n + 1) → Fin 4 → ℝ} (hx : x ∈ posOrderedEuclidN (n + 1)) :
    osTailPoint n x ∈ posOrderedEuclidN n := by
  refine orderedEuclidN_pos_of_zero_pos n (fun i hi => ?_) (fun hn => ?_)
  · simp only [osTailPoint, Pi.sub_apply, euclidTimeVec, ↓reduceIte]
    have hlt : (Fin.succ i).val + 1 < n + 1 := by
      dsimp
      omega
    have h_eq : (⟨(Fin.succ i).val + 1, hlt⟩ : Fin (n + 1)) = Fin.succ ⟨i.val + 1, hi⟩ := by
      ext
      rfl
    have hstep := hx.2 (Fin.succ i) hlt
    rw [h_eq] at hstep
    linarith
  · simp only [osTailPoint, Pi.sub_apply, euclidTimeVec, ↓reduceIte]
    have hlt : (0 : Fin (n + 1)).val + 1 < n + 1 := by
      dsimp
      omega
    have h_eq : (⟨(0 : Fin (n + 1)).val + 1, hlt⟩ : Fin (n + 1)) = Fin.succ ⟨0, hn⟩ := by
      ext
      rfl
    have hstep := hx.2 0 hlt
    rw [h_eq] at hstep
    linarith

def osIteratedFieldPre {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) :
    ∀ (n : ℕ) (_ : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ posOrderedEuclidN n → OSPreHilbertSpace D
  | 0, _, _, _ => osVacuumPre D
  | n + 1, α, x, hx =>
      osFieldPrependLM D (α 0) (x 0) (hx.1 0)
        (osIteratedFieldPre D n (Fin.tail α) (osTailPoint n x)
          (osTailPoint_mem_posOrderedEuclidN n hx))

@[simp]
lemma osIteratedFieldPre_zero {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (α : Fin 0 → ι) (x : Fin 0 → Fin 4 → ℝ)
    (hx : x ∈ posOrderedEuclidN 0) :
    osIteratedFieldPre D 0 α x hx = osVacuumPre D := rfl

@[simp]
lemma osIteratedFieldPre_succ {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (n : ℕ) (α : Fin (n + 1) → ι)
    (x : Fin (n + 1) → Fin 4 → ℝ) (hx : x ∈ posOrderedEuclidN (n + 1)) :
    osIteratedFieldPre D (n + 1) α x hx =
      osFieldPrependLM D (α 0) (x 0) (hx.1 0)
        (osIteratedFieldPre D n (Fin.tail α) (osTailPoint n x)
          (osTailPoint_mem_posOrderedEuclidN n hx)) := rfl

theorem osIteratedFieldPre_eq_osBasisPre
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) :
    ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ) (hx : x ∈ posOrderedEuclidN n),
      osIteratedFieldPre D n α x hx = osBasisPre D ⟨n, (α, ⟨x, hx⟩)⟩
  | 0, α, x, hx => by
      dsimp [osIteratedFieldPre, osVacuumPre]
      congr 1
      unfold osVacuumConfig
      apply osConfig_mk_eq
      · ext i
        exact Fin.elim0 i
      · ext i μ
        exact Fin.elim0 i
  | n + 1, α, x, hx => by
      rw [osIteratedFieldPre_succ,
          osIteratedFieldPre_eq_osBasisPre D n (Fin.tail α) (osTailPoint n x)
            (osTailPoint_mem_posOrderedEuclidN n hx)]
      unfold osFieldPrependLM
      rw [osLiftConfigMap_osBasisPre]
      congr 1
      unfold osFieldPrependConfig
      dsimp only
      exact osConfig_mk_eq (Fin.cons_self_tail α) (osPrependPoint_osTailPoint n x)

def osIteratedFieldState {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S)
    (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ) (hx : x ∈ posOrderedEuclidN n) :
    OSHilbert D :=
  toOSHilbert D (osIteratedFieldPre D n α x hx)

theorem osIteratedFieldState_eq_osBasis
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S)
    (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ) (hx : x ∈ posOrderedEuclidN n) :
    osIteratedFieldState D n α x hx = osBasis D ⟨n, (α, ⟨x, hx⟩)⟩ := by
  unfold osIteratedFieldState osBasis
  rw [osIteratedFieldPre_eq_osBasisPre]

@[simp]
theorem inner_osVacuumPre_osIteratedFieldPre
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S)
    (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ) (hx : x ∈ posOrderedEuclidN n) :
    ⟪osVacuumPre D, osIteratedFieldPre D n α x hx⟫_ℂ = D.𝒮 n α x := by
  rw [osIteratedFieldPre_eq_osBasisPre, inner_osVacuumPre_osBasisPre]

@[simp]
theorem inner_osVacuum_osIteratedFieldState
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S)
    (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ) (hx : x ∈ posOrderedEuclidN n) :
    ⟪osVacuum D, osIteratedFieldState D n α x hx⟫_ℂ = D.𝒮 n α x := by
  rw [osIteratedFieldState_eq_osBasis, inner_osVacuum_osBasis]

theorem osContractionSemigroup_osIteratedFieldState
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (hcontr : OSContractionCondition D)
    (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ) (hx : x ∈ posOrderedEuclidN n)
    (τ : ℝ) (hτ : 0 ≤ τ) :
    osContractionSemigroup D hcontr τ hτ (osIteratedFieldState D n α x hx) =
      osIteratedFieldState D n α (fun i => x i + euclidTimeVec τ)
        (timeShift_mem_posOrderedEuclidN n hx hτ) := by
  rw [osIteratedFieldState_eq_osBasis, osIteratedFieldState_eq_osBasis]
  dsimp [osBasis]
  rw [osContractionSemigroup_toOSHilbert]
  unfold osTimeShiftLM
  rw [osLiftConfigMap_osBasisPre]
  rfl

theorem osSpatialTranslate_osIteratedFieldState
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (htrans : OSTranslationInvariant D.𝒮)
    (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ) (hx : x ∈ posOrderedEuclidN n)
    (a : Fin 3 → ℝ) :
    osSpatialTranslate D htrans a (osIteratedFieldState D n α x hx) =
      osIteratedFieldState D n α (fun i => x i + euclidSpatialVec a)
        (spatialShift_mem_posOrderedEuclidN n hx a) := by
  rw [osIteratedFieldState_eq_osBasis, osIteratedFieldState_eq_osBasis]
  dsimp [osBasis]
  rw [osSpatialTranslate_toOSHilbert]
  unfold osSpatialTranslateLM
  rw [osLiftConfigMap_osBasisPre]
  rfl

def osOneParticleState {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (α₀ : ι) (x₀ : Fin 4 → ℝ) (hx₀ : 0 < x₀ 0) :
    OSHilbert D :=
  toOSHilbert D (osFieldPrependLM D α₀ x₀ hx₀ (osVacuumPre D))

theorem osOneParticleState_eq_osBasis
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (α₀ : ι) (x₀ : Fin 4 → ℝ) (hx₀ : 0 < x₀ 0) :
    osOneParticleState D α₀ x₀ hx₀ =
      osBasis D ⟨1, (fun _ => α₀, ⟨fun _ => x₀, constOne_mem_posOrderedEuclidN hx₀⟩)⟩ := by
  unfold osOneParticleState osBasis
  rw [osFieldPrependLM_osVacuumPre]

@[simp]
theorem inner_osVacuum_osOneParticleState
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (α₀ : ι) (x₀ : Fin 4 → ℝ) (hx₀ : 0 < x₀ 0) :
    ⟪osVacuum D, osOneParticleState D α₀ x₀ hx₀⟫_ℂ =
      D.𝒮 1 (fun _ => α₀) (fun _ => x₀) := by
  rw [osOneParticleState_eq_osBasis, inner_osVacuum_osBasis]

theorem osContractionSemigroup_osOneParticleState
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (hcontr : OSContractionCondition D)
    (α₀ : ι) (x₀ : Fin 4 → ℝ) (hx₀ : 0 < x₀ 0) (τ : ℝ) (hτ : 0 ≤ τ) :
    osContractionSemigroup D hcontr τ hτ (osOneParticleState D α₀ x₀ hx₀) =
      osOneParticleState D α₀ (x₀ + euclidTimeVec τ)
        (time_pos_of_add_euclidTimeVec hx₀ hτ) :=
  osContractionSemigroup_toOSHilbert_osFieldPrependLM D hcontr α₀ x₀ hx₀ τ hτ (osVacuumPre D)

theorem osSpatialTranslate_osOneParticleState
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (htrans : OSTranslationInvariant D.𝒮)
    (α₀ : ι) (x₀ : Fin 4 → ℝ) (hx₀ : 0 < x₀ 0) (a : Fin 3 → ℝ) :
    osSpatialTranslate D htrans a (osOneParticleState D α₀ x₀ hx₀) =
      osOneParticleState D α₀ (x₀ + euclidSpatialVec a)
        (time_pos_of_add_euclidSpatialVec hx₀ a) := by
  unfold osOneParticleState
  rw [osSpatialTranslate_toOSHilbert_osFieldPrependLM, osSpatialTranslateLM_vacuumPre]

theorem osSpinorRot_osOneParticleState
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (hrot : OSSpinorRotCovariant R D.𝒮)
    (U : SU2) (α₀ : ι) (x₀ : Fin 4 → ℝ) (hx₀ : 0 < x₀ 0) :
    osSpinorRot D hrot U (osOneParticleState D α₀ x₀ hx₀) =
      ∑ β₀ : ι, osSpinorRotMatrix R U⁻¹ α₀ β₀ •
        osOneParticleState D β₀ (euclidRotApply U (su2Conj U) x₀)
          (by rw [euclidRotApply_su2Conj_time]; exact hx₀) := by
  unfold osOneParticleState
  rw [osSpinorRot_toOSHilbert, osSpinorRotLM_osFieldPrependLM, osSpinorRotLM_osVacuumPre,
      map_sum]
  refine Finset.sum_congr rfl (fun β₀ _ => ?_)
  exact (toOSHilbert D).map_smul _ _

theorem inner_osOneParticleState
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S)
    (α₀ α₁ : ι) (x₀ y₀ : Fin 4 → ℝ) (hx₀ : 0 < x₀ 0) (hy₀ : 0 < y₀ 0) :
    ⟪osOneParticleState D α₀ x₀ hx₀, osOneParticleState D α₁ y₀ hy₀⟫_ℂ =
      ∑ β₀ : ι, S.C α₀ β₀ *
        D.𝒮 2 (osConcatIdx 1 1 (fun _ => β₀) (fun _ => α₁))
          (osConcatPoint 1 1 (fun _ => x₀) (fun _ => y₀)) := by
  rw [osOneParticleState_eq_osBasis, osOneParticleState_eq_osBasis, inner_osBasis]
  unfold osKernel
  dsimp only
  rw [← (Equiv.funUnique (Fin 1) ι).sum_comp]
  refine Finset.sum_congr rfl (fun β₀ _ => ?_)
  rw [Fin.prod_univ_one]
  have hβ : (fun _ : Fin 1 => (Equiv.funUnique (Fin 1) ι) β₀) = β₀ := by
    ext i
    fin_cases i
    rfl
  rw [hβ]
  rfl

namespace OSHolomorphicSemigroup

variable {R : HolomorphicLorentzRep ι} {S : StarStructure R}
  {D : OSReflectionPositiveData R S} {hcontr : OSContractionCondition D}

theorem complexSpacetimeStep_add (ℰ : OSHolomorphicSemigroup D hcontr)
    (htrans : OSTranslationInvariant D.𝒮)
    (z₁ z₂ : ℂ) (h₁ : z₁ ∈ rightHalfPlane) (h₂ : z₂ ∈ rightHalfPlane)
    (a₁ a₂ : Fin 3 → ℝ) :
    ℰ.complexSpacetimeStep htrans (z₁ + z₂) (add_mem_rightHalfPlane h₁ h₂) (a₁ + a₂) =
      (ℰ.complexSpacetimeStep htrans z₁ h₁ a₁).comp
        (ℰ.complexSpacetimeStep htrans z₂ h₂ a₂) := by
  unfold complexSpacetimeStep
  rw [ℰ.map_add z₁ z₂ h₁ h₂, osSpatialTranslate_add]
  ext x
  simp only [ContinuousLinearMap.comp_apply]
  have h_comm := ℰ.comm_spatial htrans a₁ z₂ h₂
  have h_comm_x := congrArg (fun L => L (osSpatialTranslate D htrans a₂ x)) h_comm
  dsimp at h_comm_x
  rw [← h_comm_x]

@[simp]
theorem complexSpacetimeStep_vacuum (ℰ : OSHolomorphicSemigroup D hcontr)
    (htrans : OSTranslationInvariant D.𝒮)
    (z : ℂ) (hz : z ∈ rightHalfPlane) (a : Fin 3 → ℝ) :
    ℰ.complexSpacetimeStep htrans z hz a (osVacuum D) = osVacuum D := by
  unfold complexSpacetimeStep
  simp [osSpatialTranslate_vacuum, ℰ.vacuum]

theorem complexSpacetimeStep_real_eq (ℰ : OSHolomorphicSemigroup D hcontr)
    (htrans : OSTranslationInvariant D.𝒮)
    (τ : ℝ) (hτ : 0 ≤ τ) (a : Fin 3 → ℝ) :
    ℰ.complexSpacetimeStep htrans (τ : ℂ) (ofReal_mem_rightHalfPlane hτ) a =
      (osContractionSemigroup D hcontr τ hτ).comp (osSpatialTranslate D htrans a) := by
  unfold complexSpacetimeStep
  rw [ℰ.real_eq]

end OSHolomorphicSemigroup

def osComplexPropagator {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {D : OSReflectionPositiveData R S} {hcontr : OSContractionCondition D}
    (ℰ : OSHolomorphicSemigroup D hcontr) (htrans : OSTranslationInvariant D.𝒮)
    (Ψ Φ : OSHilbert D) (z : ℂ) (hz : z ∈ rightHalfPlane) (a : Fin 3 → ℝ) : ℂ :=
  ⟪Ψ, ℰ.complexSpacetimeStep htrans z hz a Φ⟫_ℂ

def osMinkowskiPropagator {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {D : OSReflectionPositiveData R S} {hcontr : OSContractionCondition D}
    (ℰ : OSHolomorphicSemigroup D hcontr) (htrans : OSTranslationInvariant D.𝒮)
    (Ψ Φ : OSHilbert D) (a : Fin 4 → ℝ) : ℂ :=
  ⟪Ψ, ℰ.spacetimeTranslate htrans a Φ⟫_ℂ

theorem osComplexPropagator_imag_eq_osMinkowskiPropagator
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {D : OSReflectionPositiveData R S} {hcontr : OSContractionCondition D}
    (ℰ : OSHolomorphicSemigroup D hcontr) (htrans : OSTranslationInvariant D.𝒮)
    (Ψ Φ : OSHilbert D) (a : Fin 4 → ℝ) :
    osComplexPropagator ℰ htrans Ψ Φ (Complex.I * (a 0 : ℂ))
      (mul_I_mem_rightHalfPlane (a 0)) (spatialPart a) =
      osMinkowskiPropagator ℰ htrans Ψ Φ a := rfl

theorem norm_osComplexPropagator_le
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {D : OSReflectionPositiveData R S} {hcontr : OSContractionCondition D}
    (ℰ : OSHolomorphicSemigroup D hcontr) (htrans : OSTranslationInvariant D.𝒮)
    (Ψ Φ : OSHilbert D) (z : ℂ) (hz : z ∈ rightHalfPlane) (a : Fin 3 → ℝ) :
    ‖osComplexPropagator ℰ htrans Ψ Φ z hz a‖ ≤ ‖Ψ‖ * ‖Φ‖ := by
  unfold osComplexPropagator
  calc ‖⟪Ψ, ℰ.complexSpacetimeStep htrans z hz a Φ⟫_ℂ‖
    _ ≤ ‖Ψ‖ * ‖ℰ.complexSpacetimeStep htrans z hz a Φ‖ := norm_inner_le_norm _ _
    _ ≤ ‖Ψ‖ * ‖Φ‖ := mul_le_mul_of_nonneg_left
        (ℰ.norm_complexSpacetimeStep_le htrans z hz a Φ) (norm_nonneg Ψ)

theorem norm_osMinkowskiPropagator_le
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {D : OSReflectionPositiveData R S} {hcontr : OSContractionCondition D}
    (ℰ : OSHolomorphicSemigroup D hcontr) (htrans : OSTranslationInvariant D.𝒮)
    (Ψ Φ : OSHilbert D) (a : Fin 4 → ℝ) :
    ‖osMinkowskiPropagator ℰ htrans Ψ Φ a‖ ≤ ‖Ψ‖ * ‖Φ‖ :=
  norm_osComplexPropagator_le ℰ htrans Ψ Φ (Complex.I * (a 0 : ℂ))
    (mul_I_mem_rightHalfPlane (a 0)) (spatialPart a)

@[simp]
theorem osComplexPropagator_vacuum_right
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {D : OSReflectionPositiveData R S} {hcontr : OSContractionCondition D}
    (ℰ : OSHolomorphicSemigroup D hcontr) (htrans : OSTranslationInvariant D.𝒮)
    (Ψ : OSHilbert D) (z : ℂ) (hz : z ∈ rightHalfPlane) (a : Fin 3 → ℝ) :
    osComplexPropagator ℰ htrans Ψ (osVacuum D) z hz a = ⟪Ψ, osVacuum D⟫_ℂ := by
  unfold osComplexPropagator
  rw [ℰ.complexSpacetimeStep_vacuum]

@[simp]
theorem osMinkowskiPropagator_zero
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {D : OSReflectionPositiveData R S} {hcontr : OSContractionCondition D}
    (ℰ : OSHolomorphicSemigroup D hcontr) (htrans : OSTranslationInvariant D.𝒮)
    (Ψ Φ : OSHilbert D) :
    osMinkowskiPropagator ℰ htrans Ψ Φ 0 = ⟪Ψ, Φ⟫_ℂ := by
  unfold osMinkowskiPropagator
  rw [ℰ.spacetimeTranslate_zero, ContinuousLinearMap.id_apply]

theorem osComplexPropagator_real_oneParticle_eq_schwinger_twoPoint
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {D : OSReflectionPositiveData R S} {hcontr : OSContractionCondition D}
    (ℰ : OSHolomorphicSemigroup D hcontr) (htrans : OSTranslationInvariant D.𝒮)
    (α₀ α₁ : ι) (x₀ y₀ : Fin 4 → ℝ) (hx₀ : 0 < x₀ 0) (hy₀ : 0 < y₀ 0)
    (τ : ℝ) (hτ : 0 ≤ τ) (a : Fin 3 → ℝ) :
    osComplexPropagator ℰ htrans
      (osOneParticleState D α₀ x₀ hx₀)
      (osOneParticleState D α₁ y₀ hy₀)
      (τ : ℂ) (ofReal_mem_rightHalfPlane hτ) a =
      ∑ β₀ : ι, S.C α₀ β₀ *
        D.𝒮 2 (osConcatIdx 1 1 (fun _ => β₀) (fun _ => α₁))
          (osConcatPoint 1 1 (fun _ => x₀)
            (fun _ => y₀ + euclidSpatialVec a + euclidTimeVec τ)) := by
  unfold osComplexPropagator
  rw [ℰ.complexSpacetimeStep_real_eq htrans τ hτ a, ContinuousLinearMap.comp_apply,
      osSpatialTranslate_osOneParticleState D htrans α₁ y₀ hy₀ a,
      osContractionSemigroup_osOneParticleState D hcontr α₁
        (y₀ + euclidSpatialVec a) (time_pos_of_add_euclidSpatialVec hy₀ a) τ hτ,
      inner_osOneParticleState]

theorem osComplexPropagator_real_oneParticle_diag_eq
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {D : OSReflectionPositiveData R S} {hcontr : OSContractionCondition D}
    (ℰ : OSHolomorphicSemigroup D hcontr) (htrans : OSTranslationInvariant D.𝒮)
    (hdiag : DiagonalStarStructure S)
    (c : ι) (x₀ y₀ : Fin 4 → ℝ) (hx₀ : 0 < x₀ 0) (hy₀ : 0 < y₀ 0)
    (τ : ℝ) (hτ : 0 ≤ τ) (a : Fin 3 → ℝ) :
    osComplexPropagator ℰ htrans
      (osOneParticleState D c x₀ hx₀)
      (osOneParticleState D c y₀ hy₀)
      (τ : ℂ) (ofReal_mem_rightHalfPlane hτ) a =
      S.C c c *
        D.𝒮 2 (fun _ => c)
          (osConcatPoint 1 1 (fun _ => x₀)
            (fun _ => y₀ + euclidSpatialVec a + euclidTimeVec τ)) := by
  rw [osComplexPropagator_real_oneParticle_eq_schwinger_twoPoint ℰ htrans c c x₀ y₀ hx₀ hy₀ τ hτ a]
  refine (Finset.sum_eq_single c (fun b _ hbc => ?_)
    (fun hc => False.elim (hc (Finset.mem_univ c)))).trans ?_
  · rw [hdiag c b (Ne.symm hbc), zero_mul]
  · rw [osConcatIdx_one_one_const]

theorem osMinkowskiPropagator_conj_symm
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {D : OSReflectionPositiveData R S} {hcontr : OSContractionCondition D}
    (ℰ : OSHolomorphicSemigroup D hcontr) (htrans : OSTranslationInvariant D.𝒮)
    (Ψ Φ : OSHilbert D) (a : Fin 4 → ℝ) :
    star (osMinkowskiPropagator ℰ htrans Ψ Φ a) =
      osMinkowskiPropagator ℰ htrans Φ Ψ (-a) := by
  unfold osMinkowskiPropagator
  rw [← starRingEnd_apply, inner_conj_symm]
  have h_unit := (ℰ.inner_spacetimeTranslate htrans (-a)
    (ℰ.spacetimeTranslate htrans a Φ) Ψ).symm
  rw [← ContinuousLinearMap.comp_apply, ← ℰ.spacetimeTranslate_add,
      neg_add_cancel, ℰ.spacetimeTranslate_zero, ContinuousLinearMap.id_apply] at h_unit
  exact h_unit

theorem osMinkowskiPropagator_sesquilinear_eq_norm_sq
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {D : OSReflectionPositiveData R S} {hcontr : OSContractionCondition D}
    (ℰ : OSHolomorphicSemigroup D hcontr) (htrans : OSTranslationInvariant D.𝒮)
    (Ψ : OSHilbert D) (m : ℕ) (c : Fin m → ℂ) (a : Fin m → Fin 4 → ℝ) :
    (∑ j : Fin m, ∑ k : Fin m,
      star (c j) * c k * osMinkowskiPropagator ℰ htrans Ψ Ψ (a k - a j)) =
      (‖∑ k : Fin m, c k • ℰ.spacetimeTranslate htrans (a k) Ψ‖ ^ 2 : ℂ) := by
  refine (?_ : _ = ⟪∑ k : Fin m, c k • ℰ.spacetimeTranslate htrans (a k) Ψ,
      ∑ k : Fin m, c k • ℰ.spacetimeTranslate htrans (a k) Ψ⟫_ℂ).trans
    (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) _)
  rw [sum_inner]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [inner_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [inner_smul_left, inner_smul_right, mul_assoc]
  congr 2
  unfold osMinkowskiPropagator
  have h_unit := (ℰ.inner_spacetimeTranslate htrans (-a j)
    (ℰ.spacetimeTranslate htrans (a j) Ψ)
    (ℰ.spacetimeTranslate htrans (a k) Ψ)).symm
  rw [← ContinuousLinearMap.comp_apply, ← ℰ.spacetimeTranslate_add, neg_add_cancel,
      ℰ.spacetimeTranslate_zero, ContinuousLinearMap.id_apply,
      ← ContinuousLinearMap.comp_apply, ← ℰ.spacetimeTranslate_add] at h_unit
  have h_sub : -a j + a k = a k - a j := by
    ext μ
    simp [sub_eq_add_neg, add_comm]
  rw [h_sub] at h_unit
  exact h_unit.symm

theorem osMinkowskiPropagator_posDef
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {D : OSReflectionPositiveData R S} {hcontr : OSContractionCondition D}
    (ℰ : OSHolomorphicSemigroup D hcontr) (htrans : OSTranslationInvariant D.𝒮)
    (Ψ : OSHilbert D) (m : ℕ) (c : Fin m → ℂ) (a : Fin m → Fin 4 → ℝ) :
    0 ≤ RCLike.re (∑ j : Fin m, ∑ k : Fin m,
      star (c j) * c k * osMinkowskiPropagator ℰ htrans Ψ Ψ (a k - a j)) := by
  rw [osMinkowskiPropagator_sesquilinear_eq_norm_sq]
  have h_re : RCLike.re (‖∑ k : Fin m, c k • ℰ.spacetimeTranslate htrans (a k) Ψ‖ ^ 2 : ℂ) =
      ‖∑ k : Fin m, c k • ℰ.spacetimeTranslate htrans (a k) Ψ‖ ^ 2 := by
    norm_cast
  rw [h_re]
  exact sq_nonneg _

structure OSEuclideanTubeBridge (R : HolomorphicLorentzRep ι) (S : StarStructure R)
    (η : ℂ) (𝒮 : SchwingerFamily ι) where
  W : WightmanFamily ι
  E : TubeExtension W
  schwinger_eq : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
    x ∈ orderedEuclidN n → 𝒮 n α x = schwingerFromTube E n α x
  tube_covariant : TubeCovariant R E
  tube_weakLocality : TubeWeakLocality η E
  spectrum : SpectrumCondition W
  poincare : PoincareCovariant R W
  weakLocality : WeakLocality η W
  positivity : Positivity S W

def osReconstructedWightmanOfTimeCluster
    (R : HolomorphicLorentzRep ι) (S : StarStructure R) (η : ℂ) (𝒮 : SchwingerFamily ι)
    (hOS : OSAxioms R S η 𝒮)
    (hcluster : OSTimeClusterDecomposition hOS.toReflectionPositiveData)
    (ℰ : OSHolomorphicSemigroup hOS.toReflectionPositiveData
      (osContractionCondition_of_timeCluster hOS.toReflectionPositiveData
        hOS.os1_translation hcluster))
    (bridge : OSEuclideanTubeBridge R S η 𝒮) :
    OSReconstructedWightman R S η 𝒮 where
  osAxioms := hOS
  contraction := osContractionCondition_of_timeCluster hOS.toReflectionPositiveData
    hOS.os1_translation hcluster
  semigroup := ℰ
  W := bridge.W
  E := bridge.E
  schwinger_eq := bridge.schwinger_eq
  tube_covariant := bridge.tube_covariant
  tube_weakLocality := bridge.tube_weakLocality
  spectrum := bridge.spectrum
  poincare := bridge.poincare
  weakLocality := bridge.weakLocality
  positivity := bridge.positivity

def osReconstructedWightmanOfDiagonalBounded
    (R : HolomorphicLorentzRep ι) (S : StarStructure R) (η : ℂ) (𝒮 : SchwingerFamily ι)
    (hOS : OSAxioms R S η 𝒮)
    (hdiag : OSDiagonalKernelBounded S 𝒮)
    (ℰ : OSHolomorphicSemigroup hOS.toReflectionPositiveData
      (osContractionCondition_of_diagonalKernelBounded hOS.toReflectionPositiveData
        hOS.os1_translation hdiag))
    (bridge : OSEuclideanTubeBridge R S η 𝒮) :
    OSReconstructedWightman R S η 𝒮 where
  osAxioms := hOS
  contraction := osContractionCondition_of_diagonalKernelBounded hOS.toReflectionPositiveData
    hOS.os1_translation hdiag
  semigroup := ℰ
  W := bridge.W
  E := bridge.E
  schwinger_eq := bridge.schwinger_eq
  tube_covariant := bridge.tube_covariant
  tube_weakLocality := bridge.tube_weakLocality
  spectrum := bridge.spectrum
  poincare := bridge.poincare
  weakLocality := bridge.weakLocality
  positivity := bridge.positivity

theorem euclid_to_minkowski_master_of_timeCluster
    (R : HolomorphicLorentzRep ι) (S : StarStructure R) (η : ℂ) (𝒮 : SchwingerFamily ι)
    (hOS : OSAxioms R S η 𝒮)
    (hcluster : OSTimeClusterDecomposition hOS.toReflectionPositiveData)
    (ℰ : OSHolomorphicSemigroup hOS.toReflectionPositiveData
      (osContractionCondition_of_timeCluster hOS.toReflectionPositiveData
        hOS.os1_translation hcluster))
    (bridge : OSEuclideanTubeBridge R S η 𝒮) :
    ComplexCovariant R bridge.E ∧
    WightmanPCT η R bridge.W ∧
    (∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ) (hx : x ∈ posOrderedEuclidN n),
      ⟪osVacuum hOS.toReflectionPositiveData,
        osIteratedFieldState hOS.toReflectionPositiveData n α x hx⟫_ℂ =
        schwingerFromTube bridge.E n α x) ∧
    (∀ (Ψ : OSHilbert hOS.toReflectionPositiveData) (m : ℕ) (c : Fin m → ℂ)
        (a : Fin m → Fin 4 → ℝ),
      0 ≤ RCLike.re (∑ j : Fin m, ∑ k : Fin m,
        star (c j) * c k *
          osMinkowskiPropagator ℰ hOS.os1_translation Ψ Ψ (a k - a j))) := by
  let P := osReconstructedWightmanOfTimeCluster R S η 𝒮 hOS hcluster ℰ bridge
  refine ⟨P.complexCovariant, P.wightman_pct, fun n α x hx => ?_, fun Ψ m c a => ?_⟩
  · rw [inner_osVacuum_osIteratedFieldState]
    exact bridge.schwinger_eq n α x (posOrderedEuclidN_subset_orderedEuclidN n hx)
  · exact osMinkowskiPropagator_posDef ℰ hOS.os1_translation Ψ m c a

theorem euclid_to_minkowski_scalar_spin_statistics_of_timeCluster
    {η : ℂ} {𝒮 : SchwingerFamily Unit}
    (hOS : OSAxioms trivialRep trivialStarStructure η 𝒮)
    (hcluster : OSTimeClusterDecomposition hOS.toReflectionPositiveData)
    (ℰ : OSHolomorphicSemigroup hOS.toReflectionPositiveData
      (osContractionCondition_of_timeCluster hOS.toReflectionPositiveData
        hOS.os1_translation hcluster))
    (bridge : OSEuclideanTubeBridge trivialRep trivialStarStructure η 𝒮)
    (h_nondeg : ∃ (n : ℕ) (_ : 1 ≤ n) (α : Fin n → Unit)
      (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ), bridge.W n α f ≠ 0) :
    η = 1 :=
  scalar_os_spin_statistics_any_nPoint
    (osReconstructedWightmanOfTimeCluster trivialRep trivialStarStructure
      η 𝒮 hOS hcluster ℰ bridge)
    h_nondeg

theorem euclid_to_minkowski_dirac_spin_statistics_of_timeCluster
    {η : ℂ} {𝒮 : SchwingerFamily (Fin 2 ⊕ Fin 2)}
    (hOS : OSAxioms diracRep diracStarStructure η 𝒮)
    (hcluster : OSTimeClusterDecomposition hOS.toReflectionPositiveData)
    (ℰ : OSHolomorphicSemigroup hOS.toReflectionPositiveData
      (osContractionCondition_of_timeCluster hOS.toReflectionPositiveData
        hOS.os1_translation hcluster))
    (bridge : OSEuclideanTubeBridge diracRep diracStarStructure η 𝒮)
    (h_nondeg : ∃ (n : ℕ) (_ : 1 ≤ n) (α : Fin n → Fin 2 ⊕ Fin 2)
      (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ), bridge.W n α f ≠ 0) :
    η = -1 :=
  dirac_os_spin_statistics_any_nPoint_unconditional
    (osReconstructedWightmanOfTimeCluster diracRep diracStarStructure
      η 𝒮 hOS hcluster ℰ bridge)
    h_nondeg

theorem euclid_to_minkowski_spinorTensorBispinor_spin_statistics_of_timeCluster
    (m₁ m₂ : ℕ) {η : ℂ}
    {𝒮 : SchwingerFamily (((Fin m₁ → Fin 2) × (Fin m₂ → Fin 2)) ⊕
      ((Fin m₁ → Fin 2) × (Fin m₂ → Fin 2)))}
    (hOS : OSAxioms
      (directSumRep (spinorTensorRep m₁ m₂) (chiralSwapRep (spinorTensorRep m₁ m₂)))
      (spinorTensorBispinorStarStructure m₁ m₂) η 𝒮)
    (hcluster : OSTimeClusterDecomposition hOS.toReflectionPositiveData)
    (ℰ : OSHolomorphicSemigroup hOS.toReflectionPositiveData
      (osContractionCondition_of_timeCluster hOS.toReflectionPositiveData
        hOS.os1_translation hcluster))
    (bridge : OSEuclideanTubeBridge
      (directSumRep (spinorTensorRep m₁ m₂) (chiralSwapRep (spinorTensorRep m₁ m₂)))
      (spinorTensorBispinorStarStructure m₁ m₂) η 𝒮)
    (h_nondeg : ∃ (n : ℕ) (_ : 1 ≤ n)
      (α : Fin n → ((Fin m₁ → Fin 2) × (Fin m₂ → Fin 2)) ⊕
        ((Fin m₁ → Fin 2) × (Fin m₂ → Fin 2)))
      (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ), bridge.W n α f ≠ 0) :
    η = (-1 : ℂ) ^ (m₁ + m₂) :=
  spinorTensorBispinor_os_spin_statistics_any_nPoint_unconditional m₁ m₂
    (osReconstructedWightmanOfTimeCluster
      (directSumRep (spinorTensorRep m₁ m₂) (chiralSwapRep (spinorTensorRep m₁ m₂)))
      (spinorTensorBispinorStarStructure m₁ m₂)
      η 𝒮 hOS hcluster ℰ bridge)
    h_nondeg

noncomputable def laplaceExp (E : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (-z * (E : ℂ))

@[simp]
lemma laplaceExp_zero_left (z : ℂ) :
    laplaceExp 0 z = 1 := by
  simp [laplaceExp]

@[simp]
lemma laplaceExp_zero_right (E : ℝ) :
    laplaceExp E 0 = 1 := by
  simp [laplaceExp]

lemma laplaceExp_add (E : ℝ) (z₁ z₂ : ℂ) :
    laplaceExp E (z₁ + z₂) = laplaceExp E z₁ * laplaceExp E z₂ := by
  unfold laplaceExp
  rw [← Complex.exp_add]
  congr 1
  ring

lemma laplaceExp_star (E : ℝ) (z : ℂ) :
    laplaceExp E (star z) = star (laplaceExp E z) := by
  unfold laplaceExp
  change Complex.exp (-(starRingEnd ℂ z) * (E : ℂ)) =
    (starRingEnd ℂ) (Complex.exp (-z * (E : ℂ)))
  rw [← Complex.exp_conj]
  congr 1
  simp

lemma laplaceExp_ofReal (E τ : ℝ) :
    laplaceExp E (τ : ℂ) = ((Real.exp (-τ * E) : ℝ) : ℂ) := by
  unfold laplaceExp
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring

lemma norm_laplaceExp (E : ℝ) (z : ℂ) :
    ‖laplaceExp E z‖ = Real.exp (-z.re * E) := by
  unfold laplaceExp
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]

theorem norm_laplaceExp_le_one {E : ℝ} (hE : 0 ≤ E) {z : ℂ} (hz : z ∈ rightHalfPlane) :
    ‖laplaceExp E z‖ ≤ 1 := by
  rw [norm_laplaceExp, Real.exp_le_one_iff]
  have hz_re : 0 ≤ z.re := hz
  nlinarith

@[simp]
theorem norm_laplaceExp_mul_I (E t : ℝ) :
    ‖laplaceExp E (Complex.I * (t : ℂ))‖ = 1 := by
  rw [norm_laplaceExp]
  have hre : (Complex.I * (t : ℂ)).re = 0 := by simp
  rw [hre, neg_zero, zero_mul, Real.exp_zero]

theorem differentiable_laplaceExp (E : ℝ) :
    Differentiable ℂ (laplaceExp E) := by
  unfold laplaceExp
  fun_prop

theorem analyticAt_laplaceExp (E : ℝ) (z : ℂ) :
    AnalyticAt ℂ (laplaceExp E) z :=
  (differentiable_laplaceExp E).analyticAt z

theorem analyticOnNhd_laplaceExp (E : ℝ) (s : Set ℂ) :
    AnalyticOnNhd ℂ (laplaceExp E) s :=
  fun z _ => analyticAt_laplaceExp E z

theorem analyticOn_laplaceExp (E : ℝ) (s : Set ℂ) :
    AnalyticOn ℂ (laplaceExp E) s :=
  (analyticOnNhd_laplaceExp E s).analyticOn

structure OSSpectralDecomposition {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (hcontr : OSContractionCondition D) (m : ℕ) where
  E : Fin m → ℝ
  energy_nonneg : ∀ k : Fin m, 0 ≤ E k
  P : Fin m → (OSHilbert D →L[ℂ] OSHilbert D)
  proj_selfAdjoint : ∀ (k : Fin m) (x y : OSHilbert D),
    ⟪P k x, y⟫_ℂ = ⟪x, P k y⟫_ℂ
  proj_mul : ∀ (j k : Fin m),
    (P j).comp (P k) = if j = k then P j else 0
  sum_proj : ∀ x : OSHilbert D, ∑ k : Fin m, P k x = x
  semigroup_eq : ∀ (τ : ℝ) (hτ : 0 ≤ τ) (x : OSHilbert D),
    osContractionSemigroup D hcontr τ hτ x =
      ∑ k : Fin m, laplaceExp (E k) (τ : ℂ) • P k x
  vacuum_eq : ∀ z : ℂ,
    ∑ k : Fin m, laplaceExp (E k) z • P k (osVacuum D) = osVacuum D
  comm_spatial : ∀ (htrans : OSTranslationInvariant D.𝒮) (a : Fin 3 → ℝ) (k : Fin m),
    (osSpatialTranslate D htrans a).comp (P k) =
      (P k).comp (osSpatialTranslate D htrans a)

namespace OSSpectralDecomposition

variable {R : HolomorphicLorentzRep ι} {S : StarStructure R}
  {D : OSReflectionPositiveData R S} {hcontr : OSContractionCondition D} {m : ℕ}

noncomputable def entireZ (spec : OSSpectralDecomposition D hcontr m) (z : ℂ) :
    OSHilbert D →L[ℂ] OSHilbert D :=
  ∑ k : Fin m, laplaceExp (spec.E k) z • spec.P k

@[simp]
lemma entireZ_apply (spec : OSSpectralDecomposition D hcontr m) (z : ℂ) (x : OSHilbert D) :
    spec.entireZ z x = ∑ k : Fin m, laplaceExp (spec.E k) z • spec.P k x := by
  unfold entireZ
  rw [_root_.sum_apply]
  rfl

@[simp]
lemma proj_comp_self (spec : OSSpectralDecomposition D hcontr m) (k : Fin m) :
    (spec.P k).comp (spec.P k) = spec.P k := by
  rw [spec.proj_mul k k, if_pos rfl]

@[simp]
lemma proj_apply_self (spec : OSSpectralDecomposition D hcontr m) (k : Fin m) (x : OSHilbert D) :
    spec.P k (spec.P k x) = spec.P k x := by
  change ((spec.P k).comp (spec.P k)) x = spec.P k x
  rw [spec.proj_comp_self k]

lemma inner_proj_eq_of_ne (spec : OSSpectralDecomposition D hcontr m)
    {j k : Fin m} (hjk : j ≠ k) (x y : OSHilbert D) :
    ⟪spec.P j x, spec.P k y⟫_ℂ = 0 := by
  rw [spec.proj_selfAdjoint j]
  change ⟪x, ((spec.P j).comp (spec.P k)) y⟫_ℂ = 0
  rw [spec.proj_mul j k, if_neg hjk, _root_.zero_apply, inner_zero_right]

lemma inner_proj_self_eq_norm_sq (spec : OSSpectralDecomposition D hcontr m)
    (k : Fin m) (x : OSHilbert D) :
    ⟪spec.P k x, x⟫_ℂ = (‖spec.P k x‖ ^ 2 : ℂ) := by
  conv_lhs => rw [← spec.proj_apply_self k x]
  rw [spec.proj_selfAdjoint k (spec.P k x) x]
  exact inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (spec.P k x)

theorem norm_sq_eq_sum_proj (spec : OSSpectralDecomposition D hcontr m) (x : OSHilbert D) :
    ‖x‖ ^ 2 = ∑ k : Fin m, ‖spec.P k x‖ ^ 2 := by
  have h_inner : ⟪x, x⟫_ℂ = ∑ k : Fin m, (‖spec.P k x‖ ^ 2 : ℂ) := by
    calc ⟪x, x⟫_ℂ = ⟪x, ∑ k : Fin m, spec.P k x⟫_ℂ :=
          congrArg (fun y => ⟪x, y⟫_ℂ) (spec.sum_proj x).symm
      _ = ∑ k : Fin m, ⟪x, spec.P k x⟫_ℂ := inner_sum _ _ _
      _ = ∑ k : Fin m, (‖spec.P k x‖ ^ 2 : ℂ) := by
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [← spec.proj_selfAdjoint k, spec.inner_proj_self_eq_norm_sq k x]
  have h_re := congrArg RCLike.re h_inner
  rw [inner_self_eq_norm_sq (𝕜 := ℂ), map_sum] at h_re
  refine h_re.trans (Finset.sum_congr rfl (fun k _ => ?_))
  norm_cast

theorem inner_sum_smul_proj (spec : OSSpectralDecomposition D hcontr m)
    (c d : Fin m → ℂ) (x y : OSHilbert D) :
    ⟪∑ j : Fin m, c j • spec.P j x, ∑ k : Fin m, d k • spec.P k y⟫_ℂ =
      ∑ k : Fin m, star (c k) * d k * ⟪spec.P k x, spec.P k y⟫_ℂ := by
  rw [sum_inner]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [inner_sum]
  have h_term : ∀ k ∈ Finset.univ,
      ⟪c j • spec.P j x, d k • spec.P k y⟫_ℂ =
        if k = j then star (c j) * d j * ⟪spec.P j x, spec.P j y⟫_ℂ else 0 := by
    intro k _
    rw [inner_smul_left, inner_smul_right]
    by_cases hkj : k = j
    · subst hkj
      rw [if_pos rfl]
      change (starRingEnd ℂ) (c k) * (d k * ⟪spec.P k x, spec.P k y⟫_ℂ) =
        (starRingEnd ℂ) (c k) * d k * ⟪spec.P k x, spec.P k y⟫_ℂ
      ring
    · rw [if_neg hkj, spec.inner_proj_eq_of_ne (Ne.symm hkj) x y, mul_zero, mul_zero]
  rw [Finset.sum_congr rfl h_term, Finset.sum_ite_eq']
  simp

theorem norm_sq_sum_smul_proj (spec : OSSpectralDecomposition D hcontr m)
    (c : Fin m → ℂ) (x : OSHilbert D) :
    ‖∑ k : Fin m, c k • spec.P k x‖ ^ 2 =
      ∑ k : Fin m, ‖c k‖ ^ 2 * ‖spec.P k x‖ ^ 2 := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ)]
  have h := congrArg RCLike.re (spec.inner_sum_smul_proj c c x x)
  rw [h, map_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have h_pk : ⟪spec.P k x, spec.P k x⟫_ℂ = (‖spec.P k x‖ ^ 2 : ℂ) :=
    inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (spec.P k x)
  have h_ck : star (c k) * c k = (‖c k‖ ^ 2 : ℂ) := by
    change (starRingEnd ℂ) (c k) * c k = _
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    norm_cast
  rw [h_pk, h_ck]
  norm_cast

theorem entireZ_real_eq (spec : OSSpectralDecomposition D hcontr m)
    (τ : ℝ) (hτ : 0 ≤ τ) :
    spec.entireZ (τ : ℂ) = osContractionSemigroup D hcontr τ hτ := by
  ext x
  rw [entireZ_apply, spec.semigroup_eq τ hτ x]

@[simp]
theorem entireZ_zero (spec : OSSpectralDecomposition D hcontr m) :
    spec.entireZ 0 = ContinuousLinearMap.id ℂ (OSHilbert D) := by
  ext x
  rw [entireZ_apply]
  simp [spec.sum_proj x]

theorem entireZ_add (spec : OSSpectralDecomposition D hcontr m) (z₁ z₂ : ℂ) :
    spec.entireZ (z₁ + z₂) = (spec.entireZ z₁).comp (spec.entireZ z₂) := by
  ext x
  simp only [ContinuousLinearMap.comp_apply, entireZ_apply]
  have h_rhs : ∀ j : Fin m,
      laplaceExp (spec.E j) z₁ •
        spec.P j (∑ k : Fin m, laplaceExp (spec.E k) z₂ • spec.P k x) =
      laplaceExp (spec.E j) (z₁ + z₂) • spec.P j x := by
    intro j
    rw [map_sum]
    have h_inner : ∀ k ∈ Finset.univ,
        spec.P j (laplaceExp (spec.E k) z₂ • spec.P k x) =
          if k = j then laplaceExp (spec.E j) z₂ • spec.P j x else 0 := by
      intro k _
      rw [map_smul]
      change laplaceExp (spec.E k) z₂ • ((spec.P j).comp (spec.P k) x) = _
      rw [spec.proj_mul j k]
      by_cases hkj : k = j
      · subst hkj
        simp
      · rw [if_neg (Ne.symm hkj), if_neg hkj, _root_.zero_apply, smul_zero]
    rw [Finset.sum_congr rfl h_inner, Finset.sum_ite_eq']
    simp only [Finset.mem_univ, ↓reduceIte, smul_smul, ← laplaceExp_add]
  exact (Finset.sum_congr rfl (fun j _ => (h_rhs j).symm))

@[simp]
theorem entireZ_vacuum (spec : OSSpectralDecomposition D hcontr m) (z : ℂ) :
    spec.entireZ z (osVacuum D) = osVacuum D := by
  rw [entireZ_apply]
  exact spec.vacuum_eq z

theorem entireZ_contraction (spec : OSSpectralDecomposition D hcontr m)
    {z : ℂ} (hz : z ∈ rightHalfPlane) (x : OSHilbert D) :
    ‖spec.entireZ z x‖ ≤ ‖x‖ := by
  have h_sq : ‖spec.entireZ z x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [entireZ_apply, spec.norm_sq_sum_smul_proj, spec.norm_sq_eq_sum_proj x]
    refine Finset.sum_le_sum (fun k _ => ?_)
    have hk : ‖laplaceExp (spec.E k) z‖ ≤ 1 :=
      norm_laplaceExp_le_one (spec.energy_nonneg k) hz
    have hk_sq : ‖laplaceExp (spec.E k) z‖ ^ 2 ≤ 1 := by
      nlinarith [norm_nonneg (laplaceExp (spec.E k) z)]
    nlinarith [sq_nonneg ‖spec.P k x‖]
  have h_sqrt := Real.sqrt_le_sqrt h_sq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h_sqrt

theorem entireZ_adjoint_symm (spec : OSSpectralDecomposition D hcontr m)
    (z : ℂ) (x y : OSHilbert D) :
    ⟪spec.entireZ z x, y⟫_ℂ = ⟪x, spec.entireZ (star z) y⟫_ℂ := by
  rw [entireZ_apply, entireZ_apply, sum_inner, inner_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [inner_smul_left, inner_smul_right, spec.proj_selfAdjoint k, laplaceExp_star]
  rfl

theorem entireZ_comm_spatial (spec : OSSpectralDecomposition D hcontr m)
    (htrans : OSTranslationInvariant D.𝒮) (a : Fin 3 → ℝ) (z : ℂ) :
    (osSpatialTranslate D htrans a).comp (spec.entireZ z) =
      (spec.entireZ z).comp (osSpatialTranslate D htrans a) := by
  ext x
  simp only [ContinuousLinearMap.comp_apply, entireZ_apply, map_sum, map_smul]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  congr 1
  exact congrArg (fun L => L x) (spec.comm_spatial htrans a k)

noncomputable def toOSHolomorphicSemigroup (spec : OSSpectralDecomposition D hcontr m) :
    OSHolomorphicSemigroup D hcontr where
  Z z _ := spec.entireZ z
  real_eq := spec.entireZ_real_eq
  map_add z₁ z₂ _ _ := spec.entireZ_add z₁ z₂
  vacuum z _ := spec.entireZ_vacuum z
  contraction _ hz x := spec.entireZ_contraction hz x
  adjoint_symm z _ x y := spec.entireZ_adjoint_symm z x y
  comm_spatial htrans a z _ := spec.entireZ_comm_spatial htrans a z

noncomputable def entirePropagator (spec : OSSpectralDecomposition D hcontr m)
    (htrans : OSTranslationInvariant D.𝒮) (Ψ Φ : OSHilbert D) (z : ℂ) (a : Fin 3 → ℝ) : ℂ :=
  ⟪Ψ, spec.entireZ z (osSpatialTranslate D htrans a Φ)⟫_ℂ

lemma entirePropagator_eq_sum (spec : OSSpectralDecomposition D hcontr m)
    (htrans : OSTranslationInvariant D.𝒮) (Ψ Φ : OSHilbert D) (z : ℂ) (a : Fin 3 → ℝ) :
    spec.entirePropagator htrans Ψ Φ z a =
      ∑ k : Fin m,
        laplaceExp (spec.E k) z * ⟪Ψ, spec.P k (osSpatialTranslate D htrans a Φ)⟫_ℂ := by
  unfold entirePropagator
  rw [entireZ_apply, inner_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [inner_smul_right]

theorem entirePropagator_eq_osComplexPropagator (spec : OSSpectralDecomposition D hcontr m)
    (htrans : OSTranslationInvariant D.𝒮) (Ψ Φ : OSHilbert D)
    (z : ℂ) (hz : z ∈ rightHalfPlane) (a : Fin 3 → ℝ) :
    spec.entirePropagator htrans Ψ Φ z a =
      osComplexPropagator spec.toOSHolomorphicSemigroup htrans Ψ Φ z hz a :=
  rfl

theorem differentiable_entirePropagator (spec : OSSpectralDecomposition D hcontr m)
    (htrans : OSTranslationInvariant D.𝒮) (Ψ Φ : OSHilbert D) (a : Fin 3 → ℝ) :
    Differentiable ℂ (fun z : ℂ => spec.entirePropagator htrans Ψ Φ z a) := by
  have h_eq : (fun z : ℂ => spec.entirePropagator htrans Ψ Φ z a) =
      fun z : ℂ => ∑ k : Fin m,
        laplaceExp (spec.E k) z * ⟪Ψ, spec.P k (osSpatialTranslate D htrans a Φ)⟫_ℂ := by
    ext z
    exact spec.entirePropagator_eq_sum htrans Ψ Φ z a
  rw [h_eq]
  have h_term : ∀ k : Fin m,
      Differentiable ℂ (fun z : ℂ =>
        laplaceExp (spec.E k) z * ⟪Ψ, spec.P k (osSpatialTranslate D htrans a Φ)⟫_ℂ) :=
    fun k => (differentiable_laplaceExp (spec.E k)).mul (differentiable_const _)
  fun_prop

theorem analyticOnNhd_entirePropagator (spec : OSSpectralDecomposition D hcontr m)
    (htrans : OSTranslationInvariant D.𝒮) (Ψ Φ : OSHilbert D) (a : Fin 3 → ℝ) (s : Set ℂ) :
    AnalyticOnNhd ℂ (fun z : ℂ => spec.entirePropagator htrans Ψ Φ z a) s :=
  fun z _ => (spec.differentiable_entirePropagator htrans Ψ Φ a).analyticAt z

theorem analyticOn_entirePropagator (spec : OSSpectralDecomposition D hcontr m)
    (htrans : OSTranslationInvariant D.𝒮) (Ψ Φ : OSHilbert D) (a : Fin 3 → ℝ) (s : Set ℂ) :
    AnalyticOn ℂ (fun z : ℂ => spec.entirePropagator htrans Ψ Φ z a) s :=
  (spec.analyticOnNhd_entirePropagator htrans Ψ Φ a s).analyticOn

end OSSpectralDecomposition

noncomputable def rankOneProjCLM {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (e : H) : H →L[ℂ] H :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟪e, x⟫_ℂ • e
      map_add' := fun x y => by rw [inner_add_right, add_smul]
      map_smul' := fun c x => by rw [inner_smul_right, RingHom.id_apply, mul_smul] }
    (‖e‖ * ‖e‖)
    (fun x => by
      dsimp
      rw [norm_smul]
      have h_cs := norm_inner_le_norm (𝕜 := ℂ) e x
      nlinarith [norm_nonneg e, norm_nonneg x])

@[simp]
lemma rankOneProjCLM_apply {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (e x : H) :
    rankOneProjCLM e x = ⟪e, x⟫_ℂ • e := rfl

lemma rankOneProjCLM_selfAdjoint {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (e x y : H) :
    ⟪rankOneProjCLM e x, y⟫_ℂ = ⟪x, rankOneProjCLM e y⟫_ℂ := by
  simp only [rankOneProjCLM_apply, inner_smul_left, inner_smul_right, inner_conj_symm]
  ring

@[simp]
lemma rankOneProjCLM_comp_self {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {e : H} (he : ⟪e, e⟫_ℂ = 1) :
    (rankOneProjCLM e).comp (rankOneProjCLM e) = rankOneProjCLM e := by
  ext x
  simp only [ContinuousLinearMap.comp_apply, rankOneProjCLM_apply, inner_smul_right, he, mul_one]

lemma rankOneProjCLM_comp_eq_zero_of_orth {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {e₁ e₂ : H} (h12 : ⟪e₁, e₂⟫_ℂ = 0) :
    (rankOneProjCLM e₁).comp (rankOneProjCLM e₂) = 0 := by
  ext x
  simp only [ContinuousLinearMap.comp_apply, rankOneProjCLM_apply, inner_smul_right, h12,
    mul_zero, zero_smul, _root_.zero_apply]

def tubeWickTimeDiff (n : ℕ) (z : Fin n → Fin 4 → ℂ)
    (i : Fin n) (hi : i.val + 1 < n) : ℂ :=
  -Complex.I * (z ⟨i.val + 1, hi⟩ 0 - z i 0)

@[simp]
lemma re_tubeWickTimeDiff (n : ℕ) (z : Fin n → Fin 4 → ℂ)
    (i : Fin n) (hi : i.val + 1 < n) :
    (tubeWickTimeDiff n z i hi).re = (z ⟨i.val + 1, hi⟩ 0 - z i 0).im := by
  unfold tubeWickTimeDiff
  simp [Complex.mul_re]

@[simp]
lemma im_tubeWickTimeDiff (n : ℕ) (z : Fin n → Fin 4 → ℂ)
    (i : Fin n) (hi : i.val + 1 < n) :
    (tubeWickTimeDiff n z i hi).im = -(z ⟨i.val + 1, hi⟩ 0 - z i 0).re := by
  unfold tubeWickTimeDiff
  simp [Complex.mul_im]

@[simp]
theorem tubeWickTimeDiff_add_const (n : ℕ) (z : Fin n → Fin 4 → ℂ) (a : Fin 4 → ℂ)
    (i : Fin n) (hi : i.val + 1 < n) :
    tubeWickTimeDiff n (fun k => z k + a) i hi = tubeWickTimeDiff n z i hi := by
  unfold tubeWickTimeDiff
  simp only [Pi.add_apply]
  ring

@[simp]
theorem tubeWickTimeDiff_wickEmbedN (n : ℕ) (x : Fin n → Fin 4 → ℝ)
    (i : Fin n) (hi : i.val + 1 < n) :
    tubeWickTimeDiff n (wickEmbedN n x) i hi =
      ((x ⟨i.val + 1, hi⟩ 0 - x i 0 : ℝ) : ℂ) := by
  unfold tubeWickTimeDiff wickEmbedN wickEmbed
  simp only [↓reduceIte, Complex.ofReal_sub]
  calc
    -Complex.I * ((x ⟨i.val + 1, hi⟩ 0 : ℂ) * Complex.I - (x i 0 : ℂ) * Complex.I)
      = ((x ⟨i.val + 1, hi⟩ 0 : ℂ) - (x i 0 : ℂ)) * (-(Complex.I * Complex.I)) := by ring
    _ = (x ⟨i.val + 1, hi⟩ 0 : ℂ) - (x i 0 : ℂ) := by rw [Complex.I_mul_I]; ring

theorem tubeWickTimeDiff_mem_openRightHalfPlane {n : ℕ} {z : Fin n → Fin 4 → ℂ}
    (hz : z ∈ forward_tube_n n) (i : Fin n) (hi : i.val + 1 < n) :
    tubeWickTimeDiff n z i hi ∈ openRightHalfPlane := by
  change 0 < (tubeWickTimeDiff n z i hi).re
  rw [re_tubeWickTimeDiff]
  have h_cone := (hz i hi).1
  change 0 < -((z i - z ⟨i.val + 1, hi⟩) 0).im at h_cone
  simp only [Pi.sub_apply, Complex.sub_im] at h_cone ⊢
  linarith

theorem tubeWickTimeDiff_mem_rightHalfPlane {n : ℕ} {z : Fin n → Fin 4 → ℂ}
    (hz : z ∈ forward_tube_n n) (i : Fin n) (hi : i.val + 1 < n) :
    tubeWickTimeDiff n z i hi ∈ rightHalfPlane := by
  change 0 ≤ (tubeWickTimeDiff n z i hi).re
  exact le_of_lt (tubeWickTimeDiff_mem_openRightHalfPlane hz i hi)

noncomputable def tubeWickTimeDiffCLM (n : ℕ) (i : Fin n) (hi : i.val + 1 < n) :
    (Fin n → Fin 4 → ℂ) →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => tubeWickTimeDiff n z i hi
      map_add' := fun z w => by
        unfold tubeWickTimeDiff
        simp only [Pi.add_apply]
        ring
      map_smul' := fun c z => by
        unfold tubeWickTimeDiff
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }

@[simp]
lemma tubeWickTimeDiffCLM_apply (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
    (z : Fin n → Fin 4 → ℂ) :
    tubeWickTimeDiffCLM n i hi z = tubeWickTimeDiff n z i hi := rfl

theorem differentiable_tubeWickTimeDiff (n : ℕ) (i : Fin n) (hi : i.val + 1 < n) :
    Differentiable ℂ (fun z : Fin n → Fin 4 → ℂ => tubeWickTimeDiff n z i hi) :=
  (tubeWickTimeDiffCLM n i hi).differentiable

theorem analyticAt_tubeWickTimeDiff (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
    (z : Fin n → Fin 4 → ℂ) :
    AnalyticAt ℂ (fun w : Fin n → Fin 4 → ℂ => tubeWickTimeDiff n w i hi) z :=
  (tubeWickTimeDiffCLM n i hi).analyticAt z

theorem analyticOnNhd_tubeWickTimeDiff (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
    (s : Set (Fin n → Fin 4 → ℂ)) :
    AnalyticOnNhd ℂ (fun z : Fin n → Fin 4 → ℂ => tubeWickTimeDiff n z i hi) s :=
  fun z _ => analyticAt_tubeWickTimeDiff n i hi z

theorem analyticOn_tubeWickTimeDiff (n : ℕ) (i : Fin n) (hi : i.val + 1 < n)
    (s : Set (Fin n → Fin 4 → ℂ)) :
    AnalyticOn ℂ (fun z : Fin n → Fin 4 → ℂ => tubeWickTimeDiff n z i hi) s :=
  (analyticOnNhd_tubeWickTimeDiff n i hi s).analyticOn

noncomputable def spectralTwoPointTube (E : ℝ) (z : Fin 2 → Fin 4 → ℂ) : ℂ :=
  laplaceExp E (tubeWickTimeDiff 2 z 0 (by decide))

theorem differentiable_spectralTwoPointTube (E : ℝ) :
    Differentiable ℂ (spectralTwoPointTube E) :=
  (differentiable_laplaceExp E).comp (differentiable_tubeWickTimeDiff 2 0 (by decide))

theorem analyticAt_spectralTwoPointTube (E : ℝ) (z : Fin 2 → Fin 4 → ℂ) :
    AnalyticAt ℂ (spectralTwoPointTube E) z :=
  AnalyticAt.comp (g := laplaceExp E)
    (f := fun w : Fin 2 → Fin 4 → ℂ => tubeWickTimeDiff 2 w 0 (by decide))
    (analyticAt_laplaceExp E (tubeWickTimeDiff 2 z 0 (by decide)))
    (analyticAt_tubeWickTimeDiff 2 0 (by decide) z)

theorem analyticOnNhd_spectralTwoPointTube (E : ℝ) (s : Set (Fin 2 → Fin 4 → ℂ)) :
    AnalyticOnNhd ℂ (spectralTwoPointTube E) s :=
  fun z _ => analyticAt_spectralTwoPointTube E z

theorem analyticOn_spectralTwoPointTube (E : ℝ) (s : Set (Fin 2 → Fin 4 → ℂ)) :
    AnalyticOn ℂ (spectralTwoPointTube E) s :=
  (analyticOnNhd_spectralTwoPointTube E s).analyticOn

@[simp]
theorem spectralTwoPointTube_add_const (E : ℝ) (z : Fin 2 → Fin 4 → ℂ) (a : Fin 4 → ℂ) :
    spectralTwoPointTube E (fun k => z k + a) = spectralTwoPointTube E z := by
  unfold spectralTwoPointTube
  rw [tubeWickTimeDiff_add_const]

theorem norm_spectralTwoPointTube_le_one {E : ℝ} (hE : 0 ≤ E)
    {z : Fin 2 → Fin 4 → ℂ} (hz : z ∈ forward_tube_n 2) :
    ‖spectralTwoPointTube E z‖ ≤ 1 :=
  norm_laplaceExp_le_one hE (tubeWickTimeDiff_mem_rightHalfPlane hz 0 (by decide))

@[simp]
theorem spectralTwoPointTube_wickEmbedN (E : ℝ) (x : Fin 2 → Fin 4 → ℝ) :
    spectralTwoPointTube E (wickEmbedN 2 x) =
      ((Real.exp (-(x 1 0 - x 0 0) * E) : ℝ) : ℂ) := by
  unfold spectralTwoPointTube
  rw [tubeWickTimeDiff_wickEmbedN, laplaceExp_ofReal]
  rfl

def osEuclideanTubeBridgeOfTubeExtension
    (R : HolomorphicLorentzRep ι) (S : StarStructure R) (η : ℂ) (𝒮 : SchwingerFamily ι)
    (W : WightmanFamily ι) (E : TubeExtension W)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → 𝒮 n α x = schwingerFromTube E n α x)
    (h_tcov : TubeCovariant R E)
    (h_tloc : TubeWeakLocality η E)
    (h_spec : SpectrumCondition W)
    (h_poinc : PoincareCovariant R W)
    (h_loc : WeakLocality η W)
    (h_pos : Positivity S W) :
    OSEuclideanTubeBridge R S η 𝒮 where
  W := W
  E := E
  schwinger_eq := h_schw
  tube_covariant := h_tcov
  tube_weakLocality := h_tloc
  spectrum := h_spec
  poincare := h_poinc
  weakLocality := h_loc
  positivity := h_pos

def vladimirovEuclideanTubeBridge
    (R : HolomorphicLorentzRep ι) (S : StarStructure R) (W : WightmanFamily ι) {η : ℂ}
    (hspec : SpectrumCondition W) (hP : PoincareCovariant R W)
    (hloc : WeakLocality η W) (hpos : Positivity S W) :
    OSEuclideanTubeBridge R S η (vladimirovSchwinger W) :=
  osEuclideanTubeBridgeOfTubeExtension R S η (vladimirovSchwinger W)
    W (vladimirovTubeExtension R W hspec hP)
    (fun _ _ _ _ => rfl)
    (vladimirov_tubeCovariant R W hspec hP)
    (vladimirov_tubeWeakLocality R W hspec hP hloc)
    hspec hP hloc hpos

theorem osEuclideanTubeBridge_wightman_unique
    {R : HolomorphicLorentzRep ι} {S : StarStructure R} {η : ℂ} {𝒮 : SchwingerFamily ι}
    (B₁ B₂ : OSEuclideanTubeBridge R S η 𝒮)
    (hrigid : ForwardTubeRigidFromEuclid B₁.E B₂.E) :
    B₁.W = B₂.W := by
  apply wightman_eq_of_schwingerFromTube_eq B₁.E B₂.E hrigid
  intro n α x hx
  rw [← B₁.schwinger_eq n α x hx, ← B₂.schwinger_eq n α x hx]

theorem osEuclideanTubeBridge_tube_unique
    {R : HolomorphicLorentzRep ι} {S : StarStructure R} {η : ℂ} {𝒮 : SchwingerFamily ι}
    (B₁ B₂ : OSEuclideanTubeBridge R S η 𝒮)
    (hrigid : ForwardTubeRigidFromEuclid B₁.E B₂.E)
    (n : ℕ) (α : Fin n → ι) (z : Fin n → Fin 4 → ℂ) (hz : z ∈ forward_tube_n n) :
    B₁.E.H n α z = B₂.E.H n α z := by
  refine hrigid (fun m β x hx => ?_) n α z hz
  rw [← B₁.schwinger_eq m β x hx, ← B₂.schwinger_eq m β x hx]

noncomputable def euclidSpectralTwoPoint (E : ℝ) (x : Fin 2 → Fin 4 → ℝ) : ℂ :=
  laplaceExp E ((x 1 0 - x 0 0 : ℝ) : ℂ)

@[simp]
theorem spectralTwoPointTube_wickEmbedN_eq_euclidSpectralTwoPoint
    (E : ℝ) (x : Fin 2 → Fin 4 → ℝ) :
    spectralTwoPointTube E (wickEmbedN 2 x) = euclidSpectralTwoPoint E x := by
  unfold spectralTwoPointTube euclidSpectralTwoPoint
  rw [tubeWickTimeDiff_wickEmbedN]
  rfl

theorem euclidSpectralTwoPoint_eq_ofReal_exp (E : ℝ) (x : Fin 2 → Fin 4 → ℝ) :
    euclidSpectralTwoPoint E x = ((Real.exp (-(x 1 0 - x 0 0) * E) : ℝ) : ℂ) :=
  laplaceExp_ofReal E (x 1 0 - x 0 0)

@[simp]
theorem euclidSpectralTwoPoint_add_const (E : ℝ) (x : Fin 2 → Fin 4 → ℝ) (a : Fin 4 → ℝ) :
    euclidSpectralTwoPoint E (fun i => x i + a) = euclidSpectralTwoPoint E x := by
  unfold euclidSpectralTwoPoint
  simp only [Pi.add_apply, add_sub_add_right_eq_sub]

@[simp]
lemma osConcatPoint_one_one_time_diff (x y : Fin 1 → Fin 4 → ℝ) :
    osConcatPoint 1 1 x y 1 0 - osConcatPoint 1 1 x y 0 0 = x 0 0 + y 0 0 := by
  have h0 : (0 : Fin (1 + 1)) = Fin.castAdd 1 (0 : Fin 1) := rfl
  have h1 : (1 : Fin (1 + 1)) = Fin.natAdd 1 (0 : Fin 1) := rfl
  rw [h0, h1, osConcatPoint_castAdd, osConcatPoint_natAdd]
  have hrev : Fin.rev (0 : Fin 1) = 0 := rfl
  rw [hrev, euclidTimeReflect_zero_coord]
  ring

theorem euclidSpectralTwoPoint_osConcatPoint_one_one
    (E : ℝ) (x y : Fin 1 → Fin 4 → ℝ) :
    euclidSpectralTwoPoint E (osConcatPoint 1 1 x y) =
      laplaceExp E (x 0 0 : ℂ) * laplaceExp E (y 0 0 : ℂ) := by
  unfold euclidSpectralTwoPoint
  rw [osConcatPoint_one_one_time_diff, Complex.ofReal_add, laplaceExp_add]

theorem euclidSpectralTwoPoint_osConcatPoint_one_one_eq_star_mul
    (E : ℝ) (x y : Fin 1 → Fin 4 → ℝ) :
    euclidSpectralTwoPoint E (osConcatPoint 1 1 x y) =
      star (laplaceExp E (x 0 0 : ℂ)) * laplaceExp E (y 0 0 : ℂ) := by
  rw [euclidSpectralTwoPoint_osConcatPoint_one_one, ← laplaceExp_star]
  congr 2
  exact (Complex.conj_ofReal (x 0 0)).symm

theorem euclidSpectralTwoPoint_sesquilinear_eq_norm_sq
    (E : ℝ) (m : ℕ) (c : Fin m → ℂ) (x : Fin m → Fin 1 → Fin 4 → ℝ) :
    (∑ j : Fin m, ∑ k : Fin m,
      star (c j) * c k *
        euclidSpectralTwoPoint E (osConcatPoint 1 1 (x j) (x k))) =
      (‖∑ k : Fin m, c k * laplaceExp E (x k 0 0 : ℂ)‖ ^ 2 : ℂ) := by
  have h_term : ∀ j k : Fin m,
      star (c j) * c k *
        euclidSpectralTwoPoint E (osConcatPoint 1 1 (x j) (x k)) =
      star (c j * laplaceExp E (x j 0 0 : ℂ)) *
        (c k * laplaceExp E (x k 0 0 : ℂ)) := by
    intro j k
    rw [euclidSpectralTwoPoint_osConcatPoint_one_one_eq_star_mul, star_mul']
    ring
  simp_rw [h_term, ← Finset.mul_sum, ← Finset.sum_mul, ← star_sum]
  change (starRingEnd ℂ) (∑ k : Fin m, c k * laplaceExp E (x k 0 0 : ℂ)) *
      (∑ k : Fin m, c k * laplaceExp E (x k 0 0 : ℂ)) = _
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]

theorem euclidSpectralTwoPoint_reflectionPositive
    (E : ℝ) (m : ℕ) (c : Fin m → ℂ) (x : Fin m → Fin 1 → Fin 4 → ℝ) :
    0 ≤ RCLike.re (∑ j : Fin m, ∑ k : Fin m,
      star (c j) * c k *
        euclidSpectralTwoPoint E (osConcatPoint 1 1 (x j) (x k))) := by
  rw [euclidSpectralTwoPoint_sesquilinear_eq_norm_sq]
  have h_re :
      RCLike.re (‖∑ k : Fin m, c k * laplaceExp E (x k 0 0 : ℂ)‖ ^ 2 : ℂ) =
        ‖∑ k : Fin m, c k * laplaceExp E (x k 0 0 : ℂ)‖ ^ 2 := by
    norm_cast
  rw [h_re]
  exact sq_nonneg _

theorem euclidSpectralTwoPoint_timeShift_right
    (E τ : ℝ) (x y : Fin 1 → Fin 4 → ℝ) :
    euclidSpectralTwoPoint E
      (osConcatPoint 1 1 x (fun i => y i + euclidTimeVec τ)) =
      laplaceExp E (τ : ℂ) *
        euclidSpectralTwoPoint E (osConcatPoint 1 1 x y) := by
  rw [euclidSpectralTwoPoint_osConcatPoint_one_one,
      euclidSpectralTwoPoint_osConcatPoint_one_one]
  have hy : (y 0 + euclidTimeVec τ) 0 = y 0 0 + τ := by
    simp [euclidTimeVec]
  rw [hy, Complex.ofReal_add, laplaceExp_add]
  ring

theorem norm_euclidSpectralTwoPoint_timeShift_right
    (E τ : ℝ) (x y : Fin 1 → Fin 4 → ℝ) :
    ‖euclidSpectralTwoPoint E
      (osConcatPoint 1 1 x (fun i => y i + euclidTimeVec τ))‖ =
      Real.exp (-(x 0 0 + y 0 0 + τ) * E) := by
  unfold euclidSpectralTwoPoint
  rw [osConcatPoint_one_one_time_diff]
  have hy : (y 0 + euclidTimeVec τ) 0 = y 0 0 + τ := by
    simp [euclidTimeVec]
  rw [hy, norm_laplaceExp]
  congr 1
  simp only [Complex.ofReal_re]
  ring

theorem tendsto_euclidSpectralTwoPoint_timeShift_atTop_zero
    {E : ℝ} (hE : 0 < E) (x y : Fin 1 → Fin 4 → ℝ) :
    Tendsto
      (fun τ : ℝ =>
        euclidSpectralTwoPoint E
          (osConcatPoint 1 1 x (fun i => y i + euclidTimeVec τ)))
      atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp_rw [norm_euclidSpectralTwoPoint_timeShift_right]
  have h_fac : ∀ τ : ℝ,
      Real.exp (-(x 0 0 + y 0 0 + τ) * E) =
        Real.exp (-(x 0 0 + y 0 0) * E) * Real.exp (τ * (-E)) := by
    intro τ
    rw [← Real.exp_add]
    congr 1
    ring
  simp_rw [h_fac]
  have h_atBot : Tendsto (fun τ : ℝ => τ * (-E)) atTop atBot :=
    Filter.Tendsto.atTop_mul_const_of_neg (neg_lt_zero.mpr hE) tendsto_id
  have h_exp : Tendsto (fun τ : ℝ => Real.exp (τ * (-E))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp h_atBot
  simpa using h_exp.const_mul (Real.exp (-(x 0 0 + y 0 0) * E))

lemma analyticAt_finset_sum_normed {α E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (s : Finset α) {f : α → E → ℂ} {z : E}
    (hf : ∀ a ∈ s, AnalyticAt ℂ (f a) z) :
    AnalyticAt ℂ (fun w => ∑ a ∈ s, f a w) z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa using (analyticAt_const : AnalyticAt ℂ (fun _ : E => (0 : ℂ)) z)
  | insert a s ha ih =>
    have h_eq : (fun w : E => ∑ x ∈ insert a s, f x w) =
        fun w : E => f a w + ∑ x ∈ s, f x w := by
      ext w
      exact Finset.sum_insert ha
    rw [h_eq]
    exact (hf a (Finset.mem_insert_self a s)).add
      (ih (fun b hb => hf b (Finset.mem_insert_of_mem hb)))

lemma analyticAt_finset_prod_normed {α E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (s : Finset α) {f : α → E → ℂ} {z : E}
    (hf : ∀ a ∈ s, AnalyticAt ℂ (f a) z) :
    AnalyticAt ℂ (fun w => ∏ a ∈ s, f a w) z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa using (analyticAt_const : AnalyticAt ℂ (fun _ : E => (1 : ℂ)) z)
  | insert a s ha ih =>
    have h_eq : (fun w : E => ∏ x ∈ insert a s, f x w) =
        fun w : E => f a w * ∏ x ∈ s, f x w := by
      ext w
      exact Finset.prod_insert ha
    rw [h_eq]
    exact (hf a (Finset.mem_insert_self a s)).mul
      (ih (fun b hb => hf b (Finset.mem_insert_of_mem hb)))

lemma fin_sub_one_lt {n : ℕ} (i : Fin (n - 1)) : i.val < n := by
  have := i.isLt
  omega

lemma fin_sub_one_add_one_lt {n : ℕ} (i : Fin (n - 1)) : i.val + 1 < n := by
  have := i.isLt
  omega

lemma fin_sub_one_succ_lt {n : ℕ} (i : Fin (n - 1)) :
    (⟨i.val, fin_sub_one_lt i⟩ : Fin n).val + 1 < n :=
  fin_sub_one_add_one_lt i

noncomputable def spectralMultiPointTube (n : ℕ) (E : Fin (n - 1) → ℝ)
    (z : Fin n → Fin 4 → ℂ) : ℂ :=
  ∏ i : Fin (n - 1),
    laplaceExp (E i)
      (tubeWickTimeDiff n z ⟨i.val, fin_sub_one_lt i⟩ (fin_sub_one_succ_lt i))

noncomputable def euclidSpectralMultiPoint (n : ℕ) (E : Fin (n - 1) → ℝ)
    (x : Fin n → Fin 4 → ℝ) : ℂ :=
  ∏ i : Fin (n - 1),
    laplaceExp (E i)
      ((x ⟨i.val + 1, fin_sub_one_add_one_lt i⟩ 0 -
        x ⟨i.val, fin_sub_one_lt i⟩ 0 : ℝ) : ℂ)

@[simp]
theorem spectralMultiPointTube_zero (E : Fin 0 → ℝ) (z : Fin 0 → Fin 4 → ℂ) :
    spectralMultiPointTube 0 E z = 1 := by
  simp [spectralMultiPointTube]

@[simp]
theorem spectralMultiPointTube_one (E : Fin 0 → ℝ) (z : Fin 1 → Fin 4 → ℂ) :
    spectralMultiPointTube 1 E z = 1 := by
  simp [spectralMultiPointTube]

@[simp]
theorem spectralMultiPointTube_two_eq_spectralTwoPointTube
    (E : Fin 1 → ℝ) (z : Fin 2 → Fin 4 → ℂ) :
    spectralMultiPointTube 2 E z = spectralTwoPointTube (E 0) z := by
  simp [spectralMultiPointTube, spectralTwoPointTube]

@[simp]
theorem euclidSpectralMultiPoint_two_eq_euclidSpectralTwoPoint
    (E : Fin 1 → ℝ) (x : Fin 2 → Fin 4 → ℝ) :
    euclidSpectralMultiPoint 2 E x = euclidSpectralTwoPoint (E 0) x := by
  simp [euclidSpectralMultiPoint, euclidSpectralTwoPoint]

theorem differentiable_spectralMultiPointTube (n : ℕ) (E : Fin (n - 1) → ℝ) :
    Differentiable ℂ (spectralMultiPointTube n E) := by
  unfold spectralMultiPointTube
  have h_term : ∀ i : Fin (n - 1),
      Differentiable ℂ (fun z : Fin n → Fin 4 → ℂ =>
        laplaceExp (E i)
          (tubeWickTimeDiff n z ⟨i.val, fin_sub_one_lt i⟩
            (fin_sub_one_succ_lt i))) :=
    fun i => (differentiable_laplaceExp (E i)).comp
      (differentiable_tubeWickTimeDiff n ⟨i.val, fin_sub_one_lt i⟩
        (fin_sub_one_succ_lt i))
  fun_prop

theorem analyticAt_spectralMultiPointTube (n : ℕ) (E : Fin (n - 1) → ℝ)
    (z : Fin n → Fin 4 → ℂ) :
    AnalyticAt ℂ (spectralMultiPointTube n E) z := by
  unfold spectralMultiPointTube
  refine analyticAt_finset_prod_normed Finset.univ (fun i _ => ?_)
  exact AnalyticAt.comp (g := laplaceExp (E i))
    (f := fun w : Fin n → Fin 4 → ℂ =>
      tubeWickTimeDiff n w ⟨i.val, fin_sub_one_lt i⟩ (fin_sub_one_succ_lt i))
    (analyticAt_laplaceExp (E i)
      (tubeWickTimeDiff n z ⟨i.val, fin_sub_one_lt i⟩ (fin_sub_one_succ_lt i)))
    (analyticAt_tubeWickTimeDiff n ⟨i.val, fin_sub_one_lt i⟩
      (fin_sub_one_succ_lt i) z)

theorem analyticOnNhd_spectralMultiPointTube (n : ℕ) (E : Fin (n - 1) → ℝ)
    (s : Set (Fin n → Fin 4 → ℂ)) :
    AnalyticOnNhd ℂ (spectralMultiPointTube n E) s :=
  fun z _ => analyticAt_spectralMultiPointTube n E z

theorem analyticOn_spectralMultiPointTube (n : ℕ) (E : Fin (n - 1) → ℝ)
    (s : Set (Fin n → Fin 4 → ℂ)) :
    AnalyticOn ℂ (spectralMultiPointTube n E) s :=
  (analyticOnNhd_spectralMultiPointTube n E s).analyticOn

@[simp]
theorem spectralMultiPointTube_add_const (n : ℕ) (E : Fin (n - 1) → ℝ)
    (z : Fin n → Fin 4 → ℂ) (a : Fin 4 → ℂ) :
    spectralMultiPointTube n E (fun k => z k + a) = spectralMultiPointTube n E z := by
  unfold spectralMultiPointTube
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [tubeWickTimeDiff_add_const]

@[simp]
theorem euclidSpectralMultiPoint_add_const (n : ℕ) (E : Fin (n - 1) → ℝ)
    (x : Fin n → Fin 4 → ℝ) (a : Fin 4 → ℝ) :
    euclidSpectralMultiPoint n E (fun k => x k + a) = euclidSpectralMultiPoint n E x := by
  unfold euclidSpectralMultiPoint
  refine Finset.prod_congr rfl (fun i _ => ?_)
  congr 2
  simp only [Pi.add_apply]
  ring

theorem norm_spectralMultiPointTube_le_one {n : ℕ} {E : Fin (n - 1) → ℝ}
    (hE : ∀ i : Fin (n - 1), 0 ≤ E i)
    {z : Fin n → Fin 4 → ℂ} (hz : z ∈ forward_tube_n n) :
    ‖spectralMultiPointTube n E z‖ ≤ 1 := by
  unfold spectralMultiPointTube
  rw [norm_prod]
  refine Finset.prod_le_one (fun i _ => norm_nonneg _) (fun i _ => ?_)
  exact norm_laplaceExp_le_one (hE i)
    (tubeWickTimeDiff_mem_rightHalfPlane hz ⟨i.val, fin_sub_one_lt i⟩
      (fin_sub_one_succ_lt i))

@[simp]
theorem spectralMultiPointTube_wickEmbedN (n : ℕ) (E : Fin (n - 1) → ℝ)
    (x : Fin n → Fin 4 → ℝ) :
    spectralMultiPointTube n E (wickEmbedN n x) = euclidSpectralMultiPoint n E x := by
  unfold spectralMultiPointTube euclidSpectralMultiPoint
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [tubeWickTimeDiff_wickEmbedN]

def osIndexedBaseConfig (j : ℕ) (α : Fin j → ι) : OSConfig ι :=
  ⟨j, (α, ⟨euclidOrderedBasePoint j, euclidOrderedBasePoint_mem_posOrderedEuclidN j⟩)⟩

noncomputable def osBorchersVector {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (N : ℕ)
    (u : ∀ j : ℕ, (Fin j → ι) → ℂ) : OSHilbert D :=
  ∑ j ∈ Finset.range (N + 1), ∑ α : Fin j → ι,
    u j α • osBasis D (osIndexedBaseConfig j α)

noncomputable def osWavepacketVector {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (N : ℕ)
    (F : ∀ j : ℕ, (Fin j → ι) → SchwartzMap (Fin j → Fin 4 → ℝ) ℂ) : OSHilbert D :=
  osBorchersVector D N (fun j α => ∫ x : Fin j → Fin 4 → ℝ, F j α x)

theorem inner_osBorchersVector_eq_vladimirovSesquilinear
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) {W : WightmanFamily ι} (hspec : SpectrumCondition W)
    (hD : D.𝒮 = vladimirovSchwinger W) (N : ℕ)
    (u v : ∀ j : ℕ, (Fin j → ι) → ℂ) :
    ⟪osBorchersVector D N u, osBorchersVector D N v⟫_ℂ =
      vladimirovSesquilinear S W N u v := by
  unfold osBorchersVector vladimirovSesquilinear
  rw [sum_inner]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [inner_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [sum_inner]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  rw [inner_sum]
  refine Finset.sum_congr rfl (fun α' _ => ?_)
  rw [inner_smul_left, inner_smul_right, inner_osBasis, hD,
      osKernel_vladimirovSchwinger S hspec, ← Complex.star_def]
  dsimp [osIndexedBaseConfig]
  ring

theorem norm_sq_osBorchersVector_eq_vladimirovSesquilinear
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) {W : WightmanFamily ι} (hspec : SpectrumCondition W)
    (hD : D.𝒮 = vladimirovSchwinger W) (N : ℕ)
    (u : ∀ j : ℕ, (Fin j → ι) → ℂ) :
    (‖osBorchersVector D N u‖ ^ 2 : ℂ) =
      vladimirovSesquilinear S W N u u :=
  (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (osBorchersVector D N u)).symm.trans
    (inner_osBorchersVector_eq_vladimirovSesquilinear D hspec hD N u u)

theorem wightmanSesquilinear_eq_vladimirovSesquilinear
    {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    (W : WightmanFamily ι) (hspec : SpectrumCondition W) (N : ℕ)
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
          W (j + k) (Fin.append (β ∘ Fin.rev) α') (G j k α α')) =
      vladimirovSesquilinear S W N
        (fun j α => ∫ y : Fin j → Fin 4 → ℝ, F j α y)
        (fun k α' => ∫ z : Fin k → Fin 4 → ℝ, F' k α' z) := by
  unfold vladimirovSesquilinear vladimirovKernel
  refine Finset.sum_congr rfl (fun j _ => ?_)
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine Finset.sum_congr rfl (fun α _ => ?_)
  refine Finset.sum_congr rfl (fun α' _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun β _ => ?_)
  rw [W_n_eq_vladimirov_H_zero_mul_integral hspec (j + k)
      (Fin.append (β ∘ Fin.rev) α') (G j k α α')]
  have h_int : (∫ x : Fin (j + k) → Fin 4 → ℝ, G j k α α' x) =
      star (∫ y : Fin j → Fin 4 → ℝ, F j α y) *
        (∫ z : Fin k → Fin 4 → ℝ, F' k α' z) := by
    have h_fun : (fun x : Fin (j + k) → Fin 4 → ℝ => G j k α α' x) =
        fun x => ((fun y => (starRingEnd ℂ) (F j α y))
          (fun i => x (Fin.castAdd k (Fin.rev i)))) *
          ((fun z => F' k α' z) (fun i => x (Fin.natAdd j i))) := by
      ext x
      exact hG j k α α' x
    rw [h_fun, integral_split_rev_mul j k
        (fun y => (starRingEnd ℂ) (F j α y)) (fun z => F' k α' z),
        integral_conj, ← Complex.star_def]
  rw [h_int]
  ring

theorem wightmanSesquilinear_eq_inner_osWavepacketVector
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) {W : WightmanFamily ι} (hspec : SpectrumCondition W)
    (hD : D.𝒮 = vladimirovSchwinger W) (N : ℕ)
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
          W (j + k) (Fin.append (β ∘ Fin.rev) α') (G j k α α')) =
      ⟪osWavepacketVector D N F, osWavepacketVector D N F'⟫_ℂ := by
  rw [wightmanSesquilinear_eq_vladimirovSesquilinear S W hspec N F F' G hG,
      osWavepacketVector, osWavepacketVector,
      inner_osBorchersVector_eq_vladimirovSesquilinear D hspec hD N]

theorem wightmanSesquilinear_diag_eq_norm_sq_osWavepacketVector
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) {W : WightmanFamily ι} (hspec : SpectrumCondition W)
    (hD : D.𝒮 = vladimirovSchwinger W) (N : ℕ)
    (F : ∀ j : ℕ, (Fin j → ι) → SchwartzMap (Fin j → Fin 4 → ℝ) ℂ)
    (G : ∀ j k : ℕ, (Fin j → ι) → (Fin k → ι) →
      SchwartzMap (Fin (j + k) → Fin 4 → ℝ) ℂ)
    (hG : ∀ j k α α' (x : Fin (j + k) → Fin 4 → ℝ),
      G j k α α' x =
        (starRingEnd ℂ) (F j α (fun i => x (Fin.castAdd k (Fin.rev i)))) *
          F k α' (fun i => x (Fin.natAdd j i))) :
    (∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
      ∑ α : Fin j → ι, ∑ α' : Fin k → ι, ∑ β : Fin j → ι,
        (∏ i : Fin j, S.C (α i) (β i)) *
          W (j + k) (Fin.append (β ∘ Fin.rev) α') (G j k α α')) =
      (‖osWavepacketVector D N F‖ ^ 2 : ℂ) :=
  (wightmanSesquilinear_eq_inner_osWavepacketVector D hspec hD N F F G hG).trans
    (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (osWavepacketVector D N F))

namespace OSSpectralDecomposition

variable {R : HolomorphicLorentzRep ι} {S : StarStructure R}
  {D : OSReflectionPositiveData R S} {hcontr : OSContractionCondition D} {m : ℕ}

noncomputable def twoPointTubePropagator (spec : OSSpectralDecomposition D hcontr m)
    (htrans : OSTranslationInvariant D.𝒮) (Ψ Φ : OSHilbert D)
    (a : Fin 3 → ℝ) (z : Fin 2 → Fin 4 → ℂ) : ℂ :=
  spec.entirePropagator htrans Ψ Φ (tubeWickTimeDiff 2 z 0 (by decide)) a

theorem twoPointTubePropagator_eq_sum_spectralTwoPointTube
    (spec : OSSpectralDecomposition D hcontr m)
    (htrans : OSTranslationInvariant D.𝒮) (Ψ Φ : OSHilbert D)
    (a : Fin 3 → ℝ) (z : Fin 2 → Fin 4 → ℂ) :
    spec.twoPointTubePropagator htrans Ψ Φ a z =
      ∑ k : Fin m,
        spectralTwoPointTube (spec.E k) z *
          ⟪Ψ, spec.P k (osSpatialTranslate D htrans a Φ)⟫_ℂ :=
  spec.entirePropagator_eq_sum htrans Ψ Φ (tubeWickTimeDiff 2 z 0 (by decide)) a

theorem differentiable_twoPointTubePropagator
    (spec : OSSpectralDecomposition D hcontr m)
    (htrans : OSTranslationInvariant D.𝒮) (Ψ Φ : OSHilbert D) (a : Fin 3 → ℝ) :
    Differentiable ℂ (spec.twoPointTubePropagator htrans Ψ Φ a) :=
  (spec.differentiable_entirePropagator htrans Ψ Φ a).comp
    (differentiable_tubeWickTimeDiff 2 0 (by decide))

theorem analyticAt_twoPointTubePropagator
    (spec : OSSpectralDecomposition D hcontr m)
    (htrans : OSTranslationInvariant D.𝒮) (Ψ Φ : OSHilbert D)
    (a : Fin 3 → ℝ) (z : Fin 2 → Fin 4 → ℂ) :
    AnalyticAt ℂ (spec.twoPointTubePropagator htrans Ψ Φ a) z :=
  AnalyticAt.comp
    (g := fun w : ℂ => spec.entirePropagator htrans Ψ Φ w a)
    (f := fun w : Fin 2 → Fin 4 → ℂ => tubeWickTimeDiff 2 w 0 (by decide))
    ((spec.differentiable_entirePropagator htrans Ψ Φ a).analyticAt
      (tubeWickTimeDiff 2 z 0 (by decide)))
    (analyticAt_tubeWickTimeDiff 2 0 (by decide) z)

theorem analyticOnNhd_twoPointTubePropagator
    (spec : OSSpectralDecomposition D hcontr m)
    (htrans : OSTranslationInvariant D.𝒮) (Ψ Φ : OSHilbert D)
    (a : Fin 3 → ℝ) (s : Set (Fin 2 → Fin 4 → ℂ)) :
    AnalyticOnNhd ℂ (spec.twoPointTubePropagator htrans Ψ Φ a) s :=
  fun z _ => spec.analyticAt_twoPointTubePropagator htrans Ψ Φ a z

theorem analyticOn_twoPointTubePropagator
    (spec : OSSpectralDecomposition D hcontr m)
    (htrans : OSTranslationInvariant D.𝒮) (Ψ Φ : OSHilbert D)
    (a : Fin 3 → ℝ) (s : Set (Fin 2 → Fin 4 → ℂ)) :
    AnalyticOn ℂ (spec.twoPointTubePropagator htrans Ψ Φ a) s :=
  (spec.analyticOnNhd_twoPointTubePropagator htrans Ψ Φ a s).analyticOn

@[simp]
theorem twoPointTubePropagator_add_const
    (spec : OSSpectralDecomposition D hcontr m)
    (htrans : OSTranslationInvariant D.𝒮) (Ψ Φ : OSHilbert D)
    (a : Fin 3 → ℝ) (z : Fin 2 → Fin 4 → ℂ) (b : Fin 4 → ℂ) :
    spec.twoPointTubePropagator htrans Ψ Φ a (fun i => z i + b) =
      spec.twoPointTubePropagator htrans Ψ Φ a z := by
  unfold twoPointTubePropagator
  rw [tubeWickTimeDiff_add_const]

theorem twoPointTubePropagator_eq_osComplexPropagator
    (spec : OSSpectralDecomposition D hcontr m)
    (htrans : OSTranslationInvariant D.𝒮) (Ψ Φ : OSHilbert D)
    (a : Fin 3 → ℝ) {z : Fin 2 → Fin 4 → ℂ} (hz : z ∈ forward_tube_n 2) :
    spec.twoPointTubePropagator htrans Ψ Φ a z =
      osComplexPropagator spec.toOSHolomorphicSemigroup htrans Ψ Φ
        (tubeWickTimeDiff 2 z 0 (by decide))
        (tubeWickTimeDiff_mem_rightHalfPlane hz 0 (by decide)) a :=
  rfl

theorem norm_twoPointTubePropagator_le
    (spec : OSSpectralDecomposition D hcontr m)
    (htrans : OSTranslationInvariant D.𝒮) (Ψ Φ : OSHilbert D)
    (a : Fin 3 → ℝ) {z : Fin 2 → Fin 4 → ℂ} (hz : z ∈ forward_tube_n 2) :
    ‖spec.twoPointTubePropagator htrans Ψ Φ a z‖ ≤ ‖Ψ‖ * ‖Φ‖ := by
  rw [spec.twoPointTubePropagator_eq_osComplexPropagator htrans Ψ Φ a hz]
  exact norm_osComplexPropagator_le spec.toOSHolomorphicSemigroup htrans Ψ Φ
    (tubeWickTimeDiff 2 z 0 (by decide))
    (tubeWickTimeDiff_mem_rightHalfPlane hz 0 (by decide)) a

theorem twoPointTubePropagator_wickEmbedN_eq_osComplexPropagator
    (spec : OSSpectralDecomposition D hcontr m)
    (htrans : OSTranslationInvariant D.𝒮) (Ψ Φ : OSHilbert D)
    (a : Fin 3 → ℝ) {x : Fin 2 → Fin 4 → ℝ} (hx : x ∈ orderedEuclidN 2) :
    spec.twoPointTubePropagator htrans Ψ Φ a (wickEmbedN 2 x) =
      osComplexPropagator spec.toOSHolomorphicSemigroup htrans Ψ Φ
        ((x 1 0 - x 0 0 : ℝ) : ℂ)
        (ofReal_mem_rightHalfPlane (sub_nonneg.mpr (le_of_lt (hx 0 (by decide))))) a := by
  unfold twoPointTubePropagator
  rw [tubeWickTimeDiff_wickEmbedN]
  rfl

theorem twoPointTubePropagator_oneParticle_wickEmbedN_eq_schwinger
    (spec : OSSpectralDecomposition D hcontr m)
    (htrans : OSTranslationInvariant D.𝒮)
    (α₀ α₁ : ι) (x₀ y₀ : Fin 4 → ℝ) (hx₀ : 0 < x₀ 0) (hy₀ : 0 < y₀ 0)
    (a : Fin 3 → ℝ) {x : Fin 2 → Fin 4 → ℝ} (hx : x ∈ orderedEuclidN 2) :
    spec.twoPointTubePropagator htrans
      (osOneParticleState D α₀ x₀ hx₀)
      (osOneParticleState D α₁ y₀ hy₀)
      a (wickEmbedN 2 x) =
      ∑ β₀ : ι, S.C α₀ β₀ *
        D.𝒮 2 (osConcatIdx 1 1 (fun _ => β₀) (fun _ => α₁))
          (osConcatPoint 1 1 (fun _ => x₀)
            (fun _ => y₀ + euclidSpatialVec a + euclidTimeVec (x 1 0 - x 0 0))) := by
  rw [spec.twoPointTubePropagator_wickEmbedN_eq_osComplexPropagator htrans _ _ a hx]
  exact osComplexPropagator_real_oneParticle_eq_schwinger_twoPoint
    spec.toOSHolomorphicSemigroup htrans α₀ α₁ x₀ y₀ hx₀ hy₀
    (x 1 0 - x 0 0) (sub_nonneg.mpr (le_of_lt (hx 0 (by decide)))) a

end OSSpectralDecomposition

theorem osKernel_eq_vladimirovKernel_of_schwinger_eq
    {R : HolomorphicLorentzRep ι} (S : StarStructure R)
    {𝒮 : SchwingerFamily ι} {W : WightmanFamily ι} (hspec : SpectrumCondition W)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → 𝒮 n α x = vladimirovSchwinger W n α x)
    (A B : OSConfig ι) :
    osKernel S 𝒮 A B = vladimirovKernel S W A.1 B.1 A.2.1 B.2.1 := by
  rcases A with ⟨j, α, x, hx⟩
  rcases B with ⟨k, α', y, hy⟩
  dsimp [osKernel]
  have h_eq : ∀ β : Fin j → ι,
      𝒮 (j + k) (osConcatIdx j k β α') (osConcatPoint j k x y) =
        vladimirovSchwinger W (j + k) (osConcatIdx j k β α') (osConcatPoint j k x y) :=
    fun β => h_schw (j + k) (osConcatIdx j k β α') (osConcatPoint j k x y)
      (osConcatPoint_mem_orderedEuclidN j k hx hy)
  simp_rw [h_eq]
  exact osKernel_vladimirovSchwinger S hspec ⟨j, α, x, hx⟩ ⟨k, α', y, hy⟩

theorem inner_osBorchersVector_eq_vladimirovSesquilinear_of_schwinger_eq
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) {W : WightmanFamily ι} (hspec : SpectrumCondition W)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → D.𝒮 n α x = vladimirovSchwinger W n α x)
    (N : ℕ) (u v : ∀ j : ℕ, (Fin j → ι) → ℂ) :
    ⟪osBorchersVector D N u, osBorchersVector D N v⟫_ℂ =
      vladimirovSesquilinear S W N u v := by
  unfold osBorchersVector vladimirovSesquilinear
  rw [sum_inner]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [inner_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [sum_inner]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  rw [inner_sum]
  refine Finset.sum_congr rfl (fun α' _ => ?_)
  rw [inner_smul_left, inner_smul_right, inner_osBasis,
      osKernel_eq_vladimirovKernel_of_schwinger_eq S hspec h_schw, ← Complex.star_def]
  dsimp [osIndexedBaseConfig]
  ring

theorem wightmanSesquilinear_diag_eq_norm_sq_osWavepacketVector_of_schwinger_eq
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) {W : WightmanFamily ι} (hspec : SpectrumCondition W)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → D.𝒮 n α x = vladimirovSchwinger W n α x)
    (N : ℕ)
    (F : ∀ j : ℕ, (Fin j → ι) → SchwartzMap (Fin j → Fin 4 → ℝ) ℂ)
    (G : ∀ j k : ℕ, (Fin j → ι) → (Fin k → ι) →
      SchwartzMap (Fin (j + k) → Fin 4 → ℝ) ℂ)
    (hG : ∀ j k α α' (x : Fin (j + k) → Fin 4 → ℝ),
      G j k α α' x =
        (starRingEnd ℂ) (F j α (fun i => x (Fin.castAdd k (Fin.rev i)))) *
          F k α' (fun i => x (Fin.natAdd j i))) :
    (∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
      ∑ α : Fin j → ι, ∑ α' : Fin k → ι, ∑ β : Fin j → ι,
        (∏ i : Fin j, S.C (α i) (β i)) *
          W (j + k) (Fin.append (β ∘ Fin.rev) α') (G j k α α')) =
      (‖osWavepacketVector D N F‖ ^ 2 : ℂ) := by
  rw [wightmanSesquilinear_eq_vladimirovSesquilinear S W hspec N F F G hG,
      osWavepacketVector,
      ← inner_osBorchersVector_eq_vladimirovSesquilinear_of_schwinger_eq D hspec h_schw N]
  exact inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (osWavepacketVector D N F)

theorem positivity_of_schwinger_eq_vladimirovSchwinger
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) {W : WightmanFamily ι}
    (hspec : SpectrumCondition W)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → D.𝒮 n α x = vladimirovSchwinger W n α x) :
    Positivity S W := by
  intro N F G hG
  rw [wightmanSesquilinear_diag_eq_norm_sq_osWavepacketVector_of_schwinger_eq
      D hspec h_schw N F G hG]
  have h_nonneg : 0 ≤ ‖osWavepacketVector D N F‖ ^ 2 := sq_nonneg _
  exact_mod_cast h_nonneg

theorem positivity_of_osReflectionPositiveData
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) {W : WightmanFamily ι}
    (hspec : SpectrumCondition W) (hD : D.𝒮 = vladimirovSchwinger W) :
    Positivity S W :=
  positivity_of_schwinger_eq_vladimirovSchwinger D hspec (fun n α x _ => by rw [hD])

def vladimirovEuclideanTubeBridgeOfOSData
    (R : HolomorphicLorentzRep ι) (S : StarStructure R)
    (D : OSReflectionPositiveData R S) (W : WightmanFamily ι) {η : ℂ}
    (hspec : SpectrumCondition W) (hP : PoincareCovariant R W)
    (hloc : WeakLocality η W)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → D.𝒮 n α x = vladimirovSchwinger W n α x) :
    OSEuclideanTubeBridge R S η D.𝒮 :=
  osEuclideanTubeBridgeOfTubeExtension R S η D.𝒮
    W (vladimirovTubeExtension R W hspec hP)
    h_schw
    (vladimirov_tubeCovariant R W hspec hP)
    (vladimirov_tubeWeakLocality R W hspec hP hloc)
    hspec hP hloc
    (positivity_of_schwinger_eq_vladimirovSchwinger D hspec h_schw)

def vladimirovOSReconstructionOfOSReflectionPositive
    (R : HolomorphicLorentzRep ι) (S : StarStructure R)
    (W : WightmanFamily ι) {η : ℂ}
    (hspec : SpectrumCondition W) (hP : PoincareCovariant R W)
    (hloc : WeakLocality η W)
    (hherm : TubeWickHermiticity S (vladimirovTubeExtension R W hspec hP))
    (hrp : OSReflectionPositive S (vladimirovSchwinger W))
    (hcontr : OSContractionCondition
      { 𝒮 := vladimirovSchwinger W
        hermiticity := schwingerFromTube_os_hermiticity S _ hherm
        positivity := hrp })
    (ℰ : OSHolomorphicSemigroup
      { 𝒮 := vladimirovSchwinger W
        hermiticity := schwingerFromTube_os_hermiticity S _ hherm
        positivity := hrp }
      hcontr) :
    OSReconstructedWightman R S η (vladimirovSchwinger W) :=
  vladimirovOSReconstruction R S W hspec hP hloc
    (positivity_of_osReflectionPositiveData
      { 𝒮 := vladimirovSchwinger W
        hermiticity := schwingerFromTube_os_hermiticity S _ hherm
        positivity := hrp }
      hspec rfl)
    hherm hrp hcontr ℰ

def vladimirovOSReconstructedWightmanOfTimeCluster
    (R : HolomorphicLorentzRep ι) (S : StarStructure R) (η : ℂ) (𝒮 : SchwingerFamily ι)
    (hOS : OSAxioms R S η 𝒮)
    (hcluster : OSTimeClusterDecomposition hOS.toReflectionPositiveData)
    (ℰ : OSHolomorphicSemigroup hOS.toReflectionPositiveData
      (osContractionCondition_of_timeCluster hOS.toReflectionPositiveData
        hOS.os1_translation hcluster))
    (W : WightmanFamily ι)
    (hspec : SpectrumCondition W) (hP : PoincareCovariant R W) (hloc : WeakLocality η W)
    (h_schw : ∀ (n : ℕ) (α : Fin n → ι) (x : Fin n → Fin 4 → ℝ),
      x ∈ orderedEuclidN n → 𝒮 n α x = vladimirovSchwinger W n α x) :
    OSReconstructedWightman R S η 𝒮 :=
  osReconstructedWightmanOfTimeCluster R S η 𝒮 hOS hcluster ℰ
    (vladimirovEuclideanTubeBridgeOfOSData R S hOS.toReflectionPositiveData
      W hspec hP hloc h_schw)

lemma integral_fintype_count {A E : Type*} [Fintype A] [MeasurableSpace A]
    [MeasurableSingletonClass A] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : A → E) :
    (∫ a : A, f a ∂Measure.count) = ∑ a : A, f a := by
  rw [integral_fintype Integrable.of_finite]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  simp [Measure.real]

noncomputable def measureKallenLehmannTube
    {A : Type*} [MeasurableSpace A] (μ : Measure A) (w E : A → ℝ)
    (z : Fin 2 → Fin 4 → ℂ) : ℂ :=
  ∫ a : A, (w a : ℂ) * spectralTwoPointTube (E a) z ∂μ

noncomputable def measureKallenLehmannEuclid
    {A : Type*} [MeasurableSpace A] (μ : Measure A) (w E : A → ℝ)
    (x : Fin 2 → Fin 4 → ℝ) : ℂ :=
  ∫ a : A, (w a : ℂ) * euclidSpectralTwoPoint (E a) x ∂μ

@[simp]
theorem measureKallenLehmannTube_wickEmbedN
    {A : Type*} [MeasurableSpace A] (μ : Measure A) (w E : A → ℝ)
    (x : Fin 2 → Fin 4 → ℝ) :
    measureKallenLehmannTube μ w E (wickEmbedN 2 x) =
      measureKallenLehmannEuclid μ w E x := by
  unfold measureKallenLehmannTube measureKallenLehmannEuclid
  simp_rw [spectralTwoPointTube_wickEmbedN_eq_euclidSpectralTwoPoint]

@[simp]
theorem measureKallenLehmannTube_add_const
    {A : Type*} [MeasurableSpace A] (μ : Measure A) (w E : A → ℝ)
    (z : Fin 2 → Fin 4 → ℂ) (b : Fin 4 → ℂ) :
    measureKallenLehmannTube μ w E (fun i => z i + b) =
      measureKallenLehmannTube μ w E z := by
  unfold measureKallenLehmannTube
  simp_rw [spectralTwoPointTube_add_const]

@[simp]
theorem measureKallenLehmannEuclid_add_const
    {A : Type*} [MeasurableSpace A] (μ : Measure A) (w E : A → ℝ)
    (x : Fin 2 → Fin 4 → ℝ) (b : Fin 4 → ℝ) :
    measureKallenLehmannEuclid μ w E (fun i => x i + b) =
      measureKallenLehmannEuclid μ w E x := by
  unfold measureKallenLehmannEuclid
  simp_rw [euclidSpectralTwoPoint_add_const]

theorem norm_measureKallenLehmannTube_le_integral_norm
    {A : Type*} [MeasurableSpace A] (μ : Measure A) (w E : A → ℝ)
    (z : Fin 2 → Fin 4 → ℂ) :
    ‖measureKallenLehmannTube μ w E z‖ ≤
      ∫ a : A, ‖(w a : ℂ) * spectralTwoPointTube (E a) z‖ ∂μ :=
  norm_integral_le_integral_norm _

theorem norm_measureKallenLehmannTube_integrand_le
    {A : Type*} {w E : A → ℝ} {a : A} (hw : 0 ≤ w a) (hE : 0 ≤ E a)
    {z : Fin 2 → Fin 4 → ℂ} (hz : z ∈ forward_tube_n 2) :
    ‖(w a : ℂ) * spectralTwoPointTube (E a) z‖ ≤ w a := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hw]
  have h_le := norm_spectralTwoPointTube_le_one hE hz
  nlinarith

theorem measureKallenLehmannEuclid_sesquilinear_integrand_eq
    {A : Type*} (w E : A → ℝ) (a : A)
    (m : ℕ) (c : Fin m → ℂ) (x : Fin m → Fin 1 → Fin 4 → ℝ) :
    (∑ j : Fin m, ∑ k : Fin m,
      (w a : ℂ) * (star (c j) * c k *
        euclidSpectralTwoPoint (E a) (osConcatPoint 1 1 (x j) (x k)))) =
      (w a : ℂ) *
        (‖∑ k : Fin m, c k * laplaceExp (E a) (x k 0 0 : ℂ)‖ ^ 2 : ℂ) := by
  simp_rw [← Finset.mul_sum]
  rw [euclidSpectralTwoPoint_sesquilinear_eq_norm_sq]

theorem measureKallenLehmannEuclid_sesquilinear_eq_of_fintype
    {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (w E : A → ℝ) (m : ℕ) (c : Fin m → ℂ) (x : Fin m → Fin 1 → Fin 4 → ℝ) :
    (∑ j : Fin m, ∑ k : Fin m,
      star (c j) * c k *
        measureKallenLehmannEuclid Measure.count w E (osConcatPoint 1 1 (x j) (x k))) =
      ∑ a : A, (w a : ℂ) *
        (‖∑ k : Fin m, c k * laplaceExp (E a) (x k 0 0 : ℂ)‖ ^ 2 : ℂ) := by
  unfold measureKallenLehmannEuclid
  simp_rw [integral_fintype_count, Finset.mul_sum]
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
  simp_rw [h_pull]
  exact measureKallenLehmannEuclid_sesquilinear_integrand_eq w E a m c x

theorem measureKallenLehmannEuclid_reflectionPositive_of_finite
    {A : Type*} [Finite A] [MeasurableSpace A] [MeasurableSingletonClass A]
    {w : A → ℝ} (hw : ∀ a : A, 0 ≤ w a) (E : A → ℝ)
    (m : ℕ) (c : Fin m → ℂ) (x : Fin m → Fin 1 → Fin 4 → ℝ) :
    0 ≤ RCLike.re (∑ j : Fin m, ∑ k : Fin m,
      star (c j) * c k *
        measureKallenLehmannEuclid Measure.count w E (osConcatPoint 1 1 (x j) (x k))) := by
  cases nonempty_fintype A
  rw [measureKallenLehmannEuclid_sesquilinear_eq_of_fintype, map_sum]
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

structure OSSpectralMeasure {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    (D : OSReflectionPositiveData R S) (hcontr : OSContractionCondition D)
    (A : Type*) [MeasurableSpace A] where
  μ : Measure A
  E : A → ℝ
  energy_nonneg : ∀ a : A, 0 ≤ E a
  P : A → (OSHilbert D →L[ℂ] OSHilbert D)
  proj_selfAdjoint : ∀ (a : A) (x y : OSHilbert D),
    ⟪P a x, y⟫_ℂ = ⟪x, P a y⟫_ℂ
  proj_idem : ∀ (a : A) (x : OSHilbert D),
    P a (P a x) = P a x
  norm_sq_eq_integral : ∀ x : OSHilbert D,
    ‖x‖ ^ 2 = ∫ a : A, ‖P a x‖ ^ 2 ∂μ
  semigroup_inner_eq : ∀ (τ : ℝ) (hτ : 0 ≤ τ) (x y : OSHilbert D),
    ⟪x, osContractionSemigroup D hcontr τ hτ y⟫_ℂ =
      ∫ a : A, laplaceExp (E a) (τ : ℂ) * ⟪x, P a y⟫_ℂ ∂μ
  comm_spatial : ∀ (htrans : OSTranslationInvariant D.𝒮) (b : Fin 3 → ℝ) (a : A),
    (osSpatialTranslate D htrans b).comp (P a) =
      (P a).comp (osSpatialTranslate D htrans b)

namespace OSSpectralMeasure

variable {R : HolomorphicLorentzRep ι} {S : StarStructure R}
  {D : OSReflectionPositiveData R S} {hcontr : OSContractionCondition D}
  {A : Type*} [MeasurableSpace A]

theorem inner_proj_self_eq_norm_sq (M : OSSpectralMeasure D hcontr A)
    (a : A) (x : OSHilbert D) :
    ⟪x, M.P a x⟫_ℂ = (‖M.P a x‖ ^ 2 : ℂ) := by
  conv_lhs => rw [← M.proj_idem a x]
  rw [← M.proj_selfAdjoint a x (M.P a x)]
  exact inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (M.P a x)

noncomputable def propagator (M : OSSpectralMeasure D hcontr A)
    (htrans : OSTranslationInvariant D.𝒮) (Ψ Φ : OSHilbert D)
    (z : ℂ) (b : Fin 3 → ℝ) : ℂ :=
  ∫ a : A, laplaceExp (M.E a) z * ⟪Ψ, M.P a (osSpatialTranslate D htrans b Φ)⟫_ℂ ∂M.μ

noncomputable def twoPointTubePropagator (M : OSSpectralMeasure D hcontr A)
    (htrans : OSTranslationInvariant D.𝒮) (Ψ Φ : OSHilbert D)
    (b : Fin 3 → ℝ) (z : Fin 2 → Fin 4 → ℂ) : ℂ :=
  M.propagator htrans Ψ Φ (tubeWickTimeDiff 2 z 0 (by decide)) b

theorem twoPointTubePropagator_eq_integral_spectralTwoPointTube
    (M : OSSpectralMeasure D hcontr A)
    (htrans : OSTranslationInvariant D.𝒮) (Ψ Φ : OSHilbert D)
    (b : Fin 3 → ℝ) (z : Fin 2 → Fin 4 → ℂ) :
    M.twoPointTubePropagator htrans Ψ Φ b z =
      ∫ a : A,
        spectralTwoPointTube (M.E a) z *
          ⟪Ψ, M.P a (osSpatialTranslate D htrans b Φ)⟫_ℂ ∂M.μ :=
  rfl

@[simp]
theorem twoPointTubePropagator_add_const
    (M : OSSpectralMeasure D hcontr A)
    (htrans : OSTranslationInvariant D.𝒮) (Ψ Φ : OSHilbert D)
    (b : Fin 3 → ℝ) (z : Fin 2 → Fin 4 → ℂ) (c : Fin 4 → ℂ) :
    M.twoPointTubePropagator htrans Ψ Φ b (fun i => z i + c) =
      M.twoPointTubePropagator htrans Ψ Φ b z := by
  unfold twoPointTubePropagator
  rw [tubeWickTimeDiff_add_const]

theorem twoPointTubePropagator_diag_zero_eq_measureKallenLehmannTube
    (M : OSSpectralMeasure D hcontr A)
    (htrans : OSTranslationInvariant D.𝒮) (Ψ : OSHilbert D)
    (z : Fin 2 → Fin 4 → ℂ) :
    M.twoPointTubePropagator htrans Ψ Ψ 0 z =
      measureKallenLehmannTube M.μ (fun a => ‖M.P a Ψ‖ ^ 2) M.E z := by
  unfold twoPointTubePropagator propagator measureKallenLehmannTube
  refine integral_congr_ae (Filter.Eventually.of_forall (fun a => ?_))
  dsimp
  rw [osSpatialTranslate_zero, ContinuousLinearMap.id_apply,
      M.inner_proj_self_eq_norm_sq a Ψ, ← Complex.ofReal_pow, mul_comm]
  rfl

theorem twoPointTubePropagator_wickEmbedN_eq_osContractionSemigroup
    (M : OSSpectralMeasure D hcontr A)
    (htrans : OSTranslationInvariant D.𝒮) (Ψ Φ : OSHilbert D)
    (b : Fin 3 → ℝ) {x : Fin 2 → Fin 4 → ℝ} (hx : x ∈ orderedEuclidN 2) :
    M.twoPointTubePropagator htrans Ψ Φ b (wickEmbedN 2 x) =
      ⟪Ψ, osContractionSemigroup D hcontr (x 1 0 - x 0 0)
        (sub_nonneg.mpr (le_of_lt (hx 0 (by decide))))
        (osSpatialTranslate D htrans b Φ)⟫_ℂ := by
  unfold twoPointTubePropagator
  have h_time : tubeWickTimeDiff 2 (wickEmbedN 2 x) 0 (by decide) =
      ((x 1 0 - x 0 0 : ℝ) : ℂ) :=
    tubeWickTimeDiff_wickEmbedN 2 x 0 (by decide)
  rw [h_time]
  exact (M.semigroup_inner_eq (x 1 0 - x 0 0)
    (sub_nonneg.mpr (le_of_lt (hx 0 (by decide))))
    Ψ (osSpatialTranslate D htrans b Φ)).symm

theorem twoPointTubePropagator_oneParticle_wickEmbedN_eq_schwinger
    (M : OSSpectralMeasure D hcontr A)
    (htrans : OSTranslationInvariant D.𝒮)
    (α₀ α₁ : ι) (x₀ y₀ : Fin 4 → ℝ) (hx₀ : 0 < x₀ 0) (hy₀ : 0 < y₀ 0)
    (b : Fin 3 → ℝ) {x : Fin 2 → Fin 4 → ℝ} (hx : x ∈ orderedEuclidN 2) :
    M.twoPointTubePropagator htrans
      (osOneParticleState D α₀ x₀ hx₀)
      (osOneParticleState D α₁ y₀ hy₀)
      b (wickEmbedN 2 x) =
      ∑ β₀ : ι, S.C α₀ β₀ *
        D.𝒮 2 (osConcatIdx 1 1 (fun _ => β₀) (fun _ => α₁))
          (osConcatPoint 1 1 (fun _ => x₀)
            (fun _ => y₀ + euclidSpatialVec b + euclidTimeVec (x 1 0 - x 0 0))) := by
  rw [M.twoPointTubePropagator_wickEmbedN_eq_osContractionSemigroup htrans _ _ b hx,
      osSpatialTranslate_osOneParticleState D htrans α₁ y₀ hy₀ b,
      osContractionSemigroup_osOneParticleState D hcontr α₁
        (y₀ + euclidSpatialVec b) (time_pos_of_add_euclidSpatialVec hy₀ b)
        (x 1 0 - x 0 0) (sub_nonneg.mpr (le_of_lt (hx 0 (by decide)))),
      inner_osOneParticleState]

end OSSpectralMeasure

noncomputable def OSSpectralDecomposition.toOSSpectralMeasure
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {D : OSReflectionPositiveData R S} {hcontr : OSContractionCondition D} {m : ℕ}
    (spec : OSSpectralDecomposition D hcontr m) :
    OSSpectralMeasure D hcontr (Fin m) where
  μ := Measure.count
  E := spec.E
  energy_nonneg := spec.energy_nonneg
  P := spec.P
  proj_selfAdjoint := spec.proj_selfAdjoint
  proj_idem := spec.proj_apply_self
  norm_sq_eq_integral x := by
    rw [integral_fintype_count]
    exact spec.norm_sq_eq_sum_proj x
  semigroup_inner_eq τ hτ x y := by
    rw [integral_fintype_count, spec.semigroup_eq τ hτ y, inner_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [inner_smul_right]
  comm_spatial := spec.comm_spatial

@[simp]
theorem OSSpectralDecomposition.toOSSpectralMeasure_twoPointTubePropagator
    {R : HolomorphicLorentzRep ι} {S : StarStructure R}
    {D : OSReflectionPositiveData R S} {hcontr : OSContractionCondition D} {m : ℕ}
    (spec : OSSpectralDecomposition D hcontr m)
    (htrans : OSTranslationInvariant D.𝒮) (Ψ Φ : OSHilbert D)
    (b : Fin 3 → ℝ) (z : Fin 2 → Fin 4 → ℂ) :
    spec.toOSSpectralMeasure.twoPointTubePropagator htrans Ψ Φ b z =
      spec.twoPointTubePropagator htrans Ψ Φ b z := by
  unfold OSSpectralMeasure.twoPointTubePropagator OSSpectralMeasure.propagator
  change (∫ a : Fin m,
      laplaceExp (spec.E a) (tubeWickTimeDiff 2 z 0 (by decide)) *
        ⟪Ψ, spec.P a (osSpatialTranslate D htrans b Φ)⟫_ℂ ∂Measure.count) =
    spec.twoPointTubePropagator htrans Ψ Φ b z
  rw [integral_fintype_count]
  exact (spec.twoPointTubePropagator_eq_sum_spectralTwoPointTube htrans Ψ Φ b z).symm

end
end QFT
