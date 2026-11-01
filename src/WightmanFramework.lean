import CovariantFields
import Minkowski
import Lightcone
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Within
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Distribution.TemperateGrowth
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars

namespace QFT

open Geometry Geometry.MatrixAnalysis MeasureTheory Filter Topology Matrix
open scoped ComplexOrder FourierTransform RealInnerProductSpace Interval ContDiff

instance (n : ℕ) : MeasureTheory.Measure.IsAddHaarMeasure
    (MeasureTheory.MeasureSpace.volume : MeasureTheory.Measure (Fin n → Fin 4 → ℝ)) :=
  MeasureTheory.Measure.instIsAddHaarMeasureForallVolumeOfMeasurableAddOfSigmaFinite

abbrev WightmanFamily (ι : Type*) : Type _ :=
  ∀ n : ℕ, (Fin n → ι) → TemperedDistribution (Fin n → Fin 4 → ℝ) ℂ

noncomputable def minkowskiFourier {n : ℕ} (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    (p : Fin n → Fin 4 → ℝ) : ℂ :=
  ∫ x : Fin n → Fin 4 → ℝ,
    f x * Complex.exp (-(Complex.I * ((∑ k, minkowskiInner (p k) (x k) : ℝ) : ℂ)))

def minkowskiPhaseLM (n : ℕ) (p : Fin n → Fin 4 → ℝ) :
    (Fin n → Fin 4 → ℝ) →ₗ[ℝ] ℝ where
  toFun x := ∑ k : Fin n, minkowskiInner (p k) (x k)
  map_add' x y := by
    simp only [Pi.add_apply]
    have h : ∀ k, minkowskiInner (p k) (x k + y k) =
        minkowskiInner (p k) (x k) + minkowskiInner (p k) (y k) := by
      intro k
      simp [minkowskiInner_explicit]
      ring
    simp_rw [h, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, RingHom.id_apply]
    have h : ∀ k, minkowskiInner (p k) (c • x k) = c * minkowskiInner (p k) (x k) := by
      intro k
      simp [minkowskiInner_explicit]
      ring
    simp_rw [h, ← Finset.mul_sum]
    rfl

noncomputable def minkowskiPhaseCLM (n : ℕ) (p : Fin n → Fin 4 → ℝ) :
    (Fin n → Fin 4 → ℝ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap (minkowskiPhaseLM n p)

lemma continuous_minkowskiPhase (n : ℕ) (p : Fin n → Fin 4 → ℝ) :
    Continuous (fun x : Fin n → Fin 4 → ℝ => ∑ k : Fin n, minkowskiInner (p k) (x k)) :=
  (minkowskiPhaseCLM n p).continuous

lemma integrable_f_mul_exp_phase (n : ℕ) (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    (p : Fin n → Fin 4 → ℝ) :
    Integrable (fun x : Fin n → Fin 4 → ℝ =>
      f x * Complex.exp (-(Complex.I * ((∑ k, minkowskiInner (p k) (x k) : ℝ) : ℂ)))) := by
  have h_norm : ∀ x : Fin n → Fin 4 → ℝ,
      ‖f x * Complex.exp (-(Complex.I * ((∑ k, minkowskiInner (p k) (x k) : ℝ) : ℂ)))‖ ≤ ‖f x‖ := by
    intro x
    rw [norm_mul]
    have h_exp : -(Complex.I * ((∑ k, minkowskiInner (p k) (x k) : ℝ) : ℂ)) =
        (-((∑ k, minkowskiInner (p k) (x k) : ℝ) : ℂ)) * Complex.I := by ring
    rw [h_exp]
    have h_real : (-((∑ k, minkowskiInner (p k) (x k) : ℝ) : ℂ)) =
        ((-∑ k, minkowskiInner (p k) (x k) : ℝ) : ℂ) := by push_cast; ring
    rw [h_real, Complex.norm_exp_ofReal_mul_I, mul_one]
  have h_cont : Continuous (fun x : Fin n → Fin 4 → ℝ =>
      f x * Complex.exp (-(Complex.I * ((∑ k, minkowskiInner (p k) (x k) : ℝ) : ℂ)))) := by
    apply f.continuous.mul
    apply Complex.continuous_exp.comp
    apply continuous_neg.comp
    apply continuous_const.mul
    apply Complex.continuous_ofReal.comp
    exact continuous_minkowskiPhase n p
  exact (f.integrable.norm.mono' h_cont.aestronglyMeasurable (ae_of_all _ h_norm))

lemma minkowskiFourier_sub (n : ℕ) (f1 f2 : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    (p : Fin n → Fin 4 → ℝ) :
    minkowskiFourier (f1 - f2) p = minkowskiFourier f1 p - minkowskiFourier f2 p := by
  dsimp [minkowskiFourier]
  have h_sub : (fun x : Fin n → Fin 4 → ℝ =>
      (f1 - f2) x * Complex.exp (-(Complex.I * ((∑ k, minkowskiInner (p k) (x k) : ℝ) : ℂ)))) =
    (fun x => f1 x * Complex.exp (-(Complex.I * ((∑ k, minkowskiInner (p k) (x k) : ℝ) : ℂ))) -
              f2 x * Complex.exp (-(Complex.I * ((∑ k, minkowskiInner (p k) (x k) : ℝ) : ℂ)))) := by
    ext x
    have h_sub_val : (f1 - f2) x = f1 x - f2 x := rfl
    rw [h_sub_val, sub_mul]
  rw [h_sub]
  exact integral_sub (integrable_f_mul_exp_phase n f1 p) (integrable_f_mul_exp_phase n f2 p)

def spectralRegion (n : ℕ) : Set (Fin n → Fin 4 → ℝ) :=
  { p | (∑ i, p i = 0) ∧
    (∀ k : Fin n, (∑ i ∈ Finset.univ.filter (fun i : Fin n => i ≤ k), p i) ∈
      closure forward_light_cone) ∧
    p = 0 }

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def SpectrumCondition (W : WightmanFamily ι) : Prop :=
  ∀ (n : ℕ) (α : Fin n → ι) (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ),
    ((∃ U : Set (Fin n → Fin 4 → ℝ), IsOpen U ∧ spectralRegion n ⊆ U ∧
      ∀ p ∈ U, minkowskiFourier f p = 0) ∨
     minkowskiFourier f 0 = 0) → W n α f = 0

def WeakLocality (η : ℂ) (W : WightmanFamily ι) : Prop :=
  ∀ (n : ℕ) (α : Fin n → ι) (f f' : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ),
    (∀ x, f x ≠ 0 → x ∈ jost_points_n n) →
    (∀ x : Fin n → Fin 4 → ℝ, f' (fun i => x (Fin.rev i)) = f x) →
    W n α f = η ^ (n * (n - 1) / 2) * W n (α ∘ Fin.rev) f'

structure StarStructure (R : HolomorphicLorentzRep ι) where
  C : Matrix ι ι ℂ
  involutive : C * C.map star = 1
  intertwine : ∀ A B : SL2C,
    C * R.σ (A, B) = (R.σ (sl2c_conj B, sl2c_conj A)).map star * C

def Positivity {R : HolomorphicLorentzRep ι} (S : StarStructure R) (W : WightmanFamily ι) :
    Prop :=
  ∀ (N : ℕ) (F : ∀ j : ℕ, (Fin j → ι) → SchwartzMap (Fin j → Fin 4 → ℝ) ℂ)
    (G : ∀ j k : ℕ, (Fin j → ι) → (Fin k → ι) →
      SchwartzMap (Fin (j + k) → Fin 4 → ℝ) ℂ),
    (∀ j k α α' (x : Fin (j + k) → Fin 4 → ℝ),
      G j k α α' x =
        (starRingEnd ℂ) (F j α (fun i => x (Fin.castAdd k (Fin.rev i)))) *
          F k α' (fun i => x (Fin.natAdd j i))) →
    0 ≤ ∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1),
      ∑ α : Fin j → ι, ∑ α' : Fin k → ι, ∑ β : Fin j → ι,
        (∏ i, S.C (α i) (β i)) * W (j + k) (Fin.append (β ∘ Fin.rev) α') (G j k α α')

structure TubeExtension (W : WightmanFamily ι) where
  H : ∀ n : ℕ, (Fin n → ι) → (Fin n → Fin 4 → ℂ) → ℂ
  analytic : ∀ n α, AnalyticOn ℂ (H n α) (forward_tube_n n)
  boundary : ∀ (n : ℕ) (α : Fin n → ι) (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    (v : Fin 4 → ℝ), v ∈ forward_light_cone →
    Tendsto (fun t : ℝ => ∫ x : Fin n → Fin 4 → ℝ,
        H n α (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ)) * f x)
      (𝓝[>] 0) (𝓝 (W n α f))

def TubeCovariant {W : WightmanFamily ι} (R : HolomorphicLorentzRep ι)
    (E : TubeExtension W) : Prop :=
  ∀ (n : ℕ) (A : SL2C) (z : Fin n → Fin 4 → ℂ),
    z ∈ forward_tube_n n → spinorPhi (A, sl2c_conj A) • z ∈ forward_tube_n n →
    ∀ α : Fin n → ι,
      E.H n α (spinorPhi (A, sl2c_conj A) • z) =
        ∑ β : Fin n → ι, (∏ i, R.rep A (α i) (β i)) * E.H n β z

def ComplexCovariant {W : WightmanFamily ι} (R : HolomorphicLorentzRep ι)
    (E : TubeExtension W) : Prop :=
  ∀ (n : ℕ) (A B : SL2C) (z : Fin n → Fin 4 → ℂ),
    z ∈ forward_tube_n n → spinorPhi (A, B) • z ∈ forward_tube_n n →
    ∀ α : Fin n → ι,
      E.H n α (spinorPhi (A, B) • z) = ∑ β : Fin n → ι, (∏ i, R.σ (A, B) (α i) (β i)) * E.H n β z

lemma lorentzOfSL2C_one : lorentzOfSL2C 1 = 1 := by
  ext i j
  dsimp [lorentzOfSL2C]
  rw [sl2c_conj_one]
  have h1 : (spinorPhi ((1 : SL2C), (1 : SL2C)) : SpecialSpecialComplexLorentzGroup) = 1 := by
    exact map_one spinorPhi
  rw [h1]
  by_cases hij : i = j
  · subst hij; simp
  · simp [Matrix.one_apply_ne hij]

lemma poincareAct_one_trans (a : Fin 4 → ℝ) (x : Fin 4 → ℝ) :
    poincareAct a 1 x = x + a := by
  dsimp [poincareAct]
  rw [lorentzOfSL2C_one, Matrix.one_mulVec]

lemma rep_one (R : HolomorphicLorentzRep ι) : R.rep 1 = 1 := map_one R.rep

lemma prod_rep_one (R : HolomorphicLorentzRep ι) (n : ℕ) (α β : Fin n → ι) :
    (∏ i : Fin n, R.rep 1 (α i) (β i)) = if α = β then 1 else 0 := by
  have h_rep : R.rep 1 = 1 := rep_one R
  simp_rw [h_rep]
  by_cases h : α = β
  · subst h; simp
  · rw [if_neg h]
    obtain ⟨i, hi⟩ : ∃ i, α i ≠ β i := by
      by_contra hc
      push Not at hc
      exact h (funext hc)
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [Matrix.one_apply_ne hi])

theorem translationInvariant_of_poincare (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (hP : PoincareCovariant R W) (n : ℕ) (a : Fin 4 → ℝ) (α : Fin n → ι)
    (f f' : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    (h_shift : ∀ x : Fin n → Fin 4 → ℝ, f' (fun i => x i + a) = f x) :
    W n α f' = W n α f := by
  have h_poincare : ∀ x : Fin n → Fin 4 → ℝ, f' (fun i => poincareAct a 1 (x i)) = f x := by
    intro x
    simp_rw [poincareAct_one_trans]
    exact h_shift x
  have h_cov := hP n a 1 f f' h_poincare α
  rw [h_cov]
  have h_sum : ∑ β : Fin n → ι, (∏ i, R.rep 1 (α i) (β i)) * W n β f = W n α f := by
    simp_rw [prod_rep_one]
    simp
  exact h_sum

lemma lorentzOfSL2C_mul (A B : SL2C) :
    lorentzOfSL2C (A * B) = lorentzOfSL2C A * lorentzOfSL2C B := by
  have h_map : (lorentzOfSL2C (A * B)).map (algebraMap ℝ ℂ) =
      ((lorentzOfSL2C A) * (lorentzOfSL2C B)).map (algebraMap ℝ ℂ) := by
    rw [lorentzOfSL2C_map, Matrix.map_mul]
    rw [lorentzOfSL2C_map, lorentzOfSL2C_map]
    have h1 : spinorPhi (A * B, sl2c_conj (A * B)) =
        spinorPhi (A, sl2c_conj A) * spinorPhi (B, sl2c_conj B) := by
      rw [sl2c_conj_mul]
      exact map_mul spinorPhi (A, sl2c_conj A) (B, sl2c_conj B)
    rw [h1]
    rfl
  ext i j
  have h_ij := congrFun (congrFun h_map i) j
  simp only [Matrix.map_apply] at h_ij
  exact Complex.ofReal_inj.mp h_ij

lemma lorentzOfSL2C_det_one (A : SL2C) :
    (lorentzOfSL2C A).det = 1 := by
  have h_map := lorentzOfSL2C_map A
  have h_det1 : ((spinorPhi (A, sl2c_conj A)).val.val).det = 1 :=
    (spinorPhi (A, sl2c_conj A)).property.2
  have h_det_alg : (algebraMap ℝ ℂ) (lorentzOfSL2C A).det =
                   ((lorentzOfSL2C A).map (algebraMap ℝ ℂ)).det :=
    (algebraMap ℝ ℂ).map_det (lorentzOfSL2C A)
  rw [h_map, h_det1] at h_det_alg
  have h_cast : ((lorentzOfSL2C A).det : ℂ) = 1 := h_det_alg
  exact Complex.ofReal_injective h_cast

noncomputable def lorentzActLM (n : ℕ) (A : SL2C) :
    (Fin n → Fin 4 → ℝ) →ₗ[ℝ] (Fin n → Fin 4 → ℝ) where
  toFun x i := (lorentzOfSL2C A).mulVec (x i)
  map_add' x y := by
    ext i
    simp only [Pi.add_apply, Matrix.mulVec_add]
  map_smul' c x := by
    ext i k
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Matrix.mulVec_smul]
    rfl

lemma lorentzActLM_mul (n : ℕ) (A B : SL2C) (x : Fin n → Fin 4 → ℝ) :
    lorentzActLM n A (lorentzActLM n B x) = lorentzActLM n (A * B) x := by
  ext i
  dsimp [lorentzActLM]
  rw [Matrix.mulVec_mulVec, ← lorentzOfSL2C_mul]

lemma lorentzActLM_one (n : ℕ) (x : Fin n → Fin 4 → ℝ) :
    lorentzActLM n 1 x = x := by
  ext i
  dsimp [lorentzActLM]
  rw [lorentzOfSL2C_one, Matrix.one_mulVec]

noncomputable def lorentzEquiv (n : ℕ) (A : SL2C) :
    (Fin n → Fin 4 → ℝ) ≃L[ℝ] (Fin n → Fin 4 → ℝ) :=
  LinearEquiv.toContinuousLinearEquiv {
    toFun := lorentzActLM n A
    invFun := lorentzActLM n A⁻¹
    left_inv := fun x => by
      rw [lorentzActLM_mul, inv_mul_cancel, lorentzActLM_one]
    right_inv := fun x => by
      rw [lorentzActLM_mul, mul_inv_cancel, lorentzActLM_one]
    map_add' := (lorentzActLM n A).map_add
    map_smul' := (lorentzActLM n A).map_smul
  }

lemma lorentzActLM_one_det (A : SL2C) :
    LinearMap.det (lorentzActLM 1 A) = 1 := by
  let e : (Fin 4 → ℝ) ≃ₗ[ℝ] (Fin 1 → Fin 4 → ℝ) :=
    (LinearEquiv.funUnique (Fin 1) ℝ (Fin 4 → ℝ)).symm
  have h_conj : lorentzActLM 1 A = LinearEquiv.conj e (Matrix.toLin' (lorentzOfSL2C A)) := by
    apply LinearMap.ext
    intro x
    apply funext
    intro i
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    rfl
  rw [h_conj, LinearEquiv.conj_apply]
  rw [LinearMap.comp_assoc]
  have h_det_conj := LinearMap.det_conj (Matrix.toLin' (lorentzOfSL2C A)) e
  rw [h_det_conj, LinearMap.det_toLin']
  exact lorentzOfSL2C_det_one A

lemma measurePreserving_lorentz_single (A : SL2C) :
    MeasurePreserving (fun x : Fin 4 → ℝ => (lorentzOfSL2C A).mulVec x) volume volume := by
  have hdet := lorentzOfSL2C_det_one A
  have h_ne : LinearMap.det (Matrix.toLin' (lorentzOfSL2C A)) ≠ 0 := by
    rw [LinearMap.det_toLin', hdet]
    exact one_ne_zero
  have h_map := Measure.map_linearMap_addHaar_eq_smul_addHaar volume h_ne
  rw [LinearMap.det_toLin', hdet] at h_map
  simp only [inv_one, abs_one, ENNReal.ofReal_one, one_smul] at h_map
  have h_cont : Continuous (fun x : Fin 4 → ℝ => (lorentzOfSL2C A).mulVec x) :=
    LinearMap.continuous_of_finiteDimensional (Matrix.toLin' (lorentzOfSL2C A))
  exact ⟨h_cont.measurable, h_map⟩

lemma measurePreserving_lorentzAct_n (n : ℕ) (A : SL2C) :
    MeasurePreserving (lorentzActLM n A) volume volume := by
  have h_pi : (lorentzActLM n A : (Fin n → Fin 4 → ℝ) → (Fin n → Fin 4 → ℝ)) =
      fun a i => (lorentzOfSL2C A).mulVec (a i) := rfl
  rw [h_pi]
  exact volume_preserving_pi (fun _ => measurePreserving_lorentz_single A)

lemma measurePreserving_lorentzEquiv_n (n : ℕ) (A : SL2C) :
    MeasurePreserving (lorentzEquiv n A) volume volume :=
  measurePreserving_lorentzAct_n n A

lemma measurePreserving_lorentzAct_one (A : SL2C) :
    MeasurePreserving (lorentzActLM 1 A) volume volume :=
  measurePreserving_lorentzAct_n 1 A

noncomputable def schwartzLorentzCLM (n : ℕ) (A : SL2C) :
    SchwartzMap (Fin n → Fin 4 → ℝ) ℂ →L[ℂ] SchwartzMap (Fin n → Fin 4 → ℝ) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (lorentzEquiv n A)

lemma schwartzLorentzCLM_apply (n : ℕ) (A : SL2C) (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    (x : Fin n → Fin 4 → ℝ) :
    schwartzLorentzCLM n A f x = f (fun i => (lorentzOfSL2C A).mulVec (x i)) := rfl

lemma schwartzLorentz_rel (n : ℕ) (A : SL2C) (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    (x : Fin n → Fin 4 → ℝ) :
    (schwartzLorentzCLM n A⁻¹ f) (fun i => (lorentzOfSL2C A).mulVec (x i)) = f x := by
  change f (lorentzActLM n A⁻¹ (lorentzActLM n A x)) = f x
  rw [lorentzActLM_mul, inv_mul_cancel, lorentzActLM_one]

lemma wightman_lorentz_cov (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (hP : PoincareCovariant R W) (n : ℕ) (A : SL2C)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) (α : Fin n → ι) :
    W n α (schwartzLorentzCLM n A⁻¹ f) =
      ∑ β : Fin n → ι, (∏ i, R.rep A (α i) (β i)) * W n β f := by
  have h_poincare : ∀ x : Fin n → Fin 4 → ℝ,
      (schwartzLorentzCLM n A⁻¹ f) (fun i => poincareAct 0 A (x i)) = f x := by
    intro x
    dsimp [poincareAct]
    simp only [add_zero]
    exact schwartzLorentz_rel n A f x
  exact hP n 0 A f (schwartzLorentzCLM n A⁻¹ f) h_poincare α

lemma closure_forward_light_cone_subset :
    closure forward_light_cone ⊆ closed_forward_light_cone :=
  closure_minimal (fun _ hx => ⟨le_of_lt hx.1, le_of_lt hx.2⟩) closed_forward_light_cone_isClosed

noncomputable def coneGap (v : Fin 4 → ℝ) : ℝ :=
  v 0 - Real.sqrt ((v 1)^2 + (v 2)^2 + (v 3)^2)

lemma coneGap_pos (v : Fin 4 → ℝ) (hv : v ∈ forward_light_cone) :
    0 < coneGap v := by
  dsimp [coneGap]
  have hv0 : 0 < v 0 := hv.1
  have hvv : 0 < minkowskiInner v v := hv.2
  rw [minkowskiInner_explicit] at hvv
  have h_sq : (v 1)^2 + (v 2)^2 + (v 3)^2 < (v 0)^2 := by linarith
  have h_pos : 0 ≤ (v 1)^2 + (v 2)^2 + (v 3)^2 := by positivity
  have h_sqrt := Real.sqrt_lt_sqrt h_pos h_sq
  rw [Real.sqrt_sq (le_of_lt hv0)] at h_sqrt
  linarith

lemma minkowskiInner_ge_coneGap (v : Fin 4 → ℝ)
    (q : Fin 4 → ℝ) (hq : q ∈ closed_forward_light_cone) :
    coneGap v * q 0 ≤ minkowskiInner q v := by
  have hq0 : 0 ≤ q 0 := hq.1
  have hqq : 0 ≤ minkowskiInner q q := hq.2
  rw [minkowskiInner_explicit] at hqq
  have hq_sq : (q 1)^2 + (q 2)^2 + (q 3)^2 ≤ (q 0)^2 := by linarith
  have hq_pos : 0 ≤ (q 1)^2 + (q 2)^2 + (q 3)^2 := by positivity
  have hCS := cauchy_schwarz_3 (q 1) (q 2) (q 3) (v 1) (v 2) (v 3)
  have h_le : q 1 * v 1 + q 2 * v 2 + q 3 * v 3 ≤
      Real.sqrt ((q 1)^2 + (q 2)^2 + (q 3)^2) * Real.sqrt ((v 1)^2 + (v 2)^2 + (v 3)^2) := by
    rw [← Real.sqrt_mul hq_pos]
    exact Real.le_sqrt_of_sq_le hCS
  have hq_sqrt : Real.sqrt ((q 1)^2 + (q 2)^2 + (q 3)^2) ≤ q 0 := by
    have h1 := Real.sqrt_le_sqrt hq_sq
    rwa [Real.sqrt_sq hq0] at h1
  have h_sp : q 1 * v 1 + q 2 * v 2 + q 3 * v 3 ≤
      q 0 * Real.sqrt ((v 1)^2 + (v 2)^2 + (v 3)^2) := by
    apply h_le.trans
    exact mul_le_mul_of_nonneg_right hq_sqrt (Real.sqrt_nonneg _)
  rw [minkowskiInner_explicit]
  dsimp [coneGap]
  calc
    (v 0 - Real.sqrt ((v 1)^2 + (v 2)^2 + (v 3)^2)) * q 0
      = q 0 * v 0 - q 0 * Real.sqrt ((v 1)^2 + (v 2)^2 + (v 3)^2) := by ring
    _ ≤ q 0 * v 0 - (q 1 * v 1 + q 2 * v 2 + q 3 * v 3) := by linarith
    _ = q 0 * v 0 - q 1 * v 1 - q 2 * v 2 - q 3 * v 3 := by ring

lemma minkowskiInner_ge_coneGap_closure (v : Fin 4 → ℝ)
    (q : Fin 4 → ℝ) (hq : q ∈ closure forward_light_cone) :
    coneGap v * q 0 ≤ minkowskiInner q v :=
  minkowskiInner_ge_coneGap v q (closure_forward_light_cone_subset hq)

def diff_z (n : ℕ) (z : Fin n → Fin 4 → ℂ) (i : Fin n) (hi : i.val + 1 < n) : Fin 4 → ℂ :=
  z i - z ⟨i.val + 1, hi⟩

lemma smul_sub_lorentz (Λ : SpecialSpecialComplexLorentzGroup) (u v : Fin 4 → ℂ) :
    Λ • (u - v) = Λ • u - Λ • v := by
  change Λ.val.val.mulVec (u - v) = Λ.val.val.mulVec u - Λ.val.val.mulVec v
  exact Matrix.mulVec_sub Λ.val.val u v

lemma smul_diff_z (n : ℕ) (Λ : SpecialSpecialComplexLorentzGroup)
    (z : Fin n → Fin 4 → ℂ) (i : Fin n) (hi : i.val + 1 < n) :
    diff_z n (Λ • z) i hi = Λ • (diff_z n z i hi) := by
  dsimp [diff_z]
  exact (smul_sub_lorentz Λ (z i) (z ⟨i.val + 1, hi⟩)).symm

def diff_im (n : ℕ) (z : Fin n → Fin 4 → ℂ) (i : Fin n) (hi : i.val + 1 < n) : Fin 4 → ℝ :=
  fun k => -((diff_z n z i hi k).im)

lemma diff_im_mem_forward_cone (n : ℕ) (z : Fin n → Fin 4 → ℂ) (hz : z ∈ forward_tube_n n)
    (i : Fin n) (hi : i.val + 1 < n) :
    diff_im n z i hi ∈ forward_light_cone :=
  hz i hi

def partial_sum_p (n : ℕ) (p : Fin n → Fin 4 → ℝ) (k : Fin n) : Fin 4 → ℝ :=
  ∑ i ∈ Finset.univ.filter (· ≤ k), p i

lemma partial_sum_p_mem_closure (n : ℕ) (p : Fin n → Fin 4 → ℝ) (hp : p ∈ spectralRegion n)
    (k : Fin n) :
    partial_sum_p n p k ∈ closure forward_light_cone :=
  hp.2.1 k

lemma partial_cone_inner_nonneg (n : ℕ) (p : Fin n → Fin 4 → ℝ) (hp : p ∈ spectralRegion n)
    (z : Fin n → Fin 4 → ℂ) (hz : z ∈ forward_tube_n n) (i : Fin n) (hi : i.val + 1 < n) :
    0 ≤ minkowskiInner (partial_sum_p n p i) (diff_im n z i hi) := by
  have hq := partial_sum_p_mem_closure n p hp i
  have hv := diff_im_mem_forward_cone n z hz i hi
  have h_bound := minkowskiInner_ge_coneGap_closure (diff_im n z i hi) (partial_sum_p n p i) hq
  have h_gap := coneGap_pos _ hv
  have hq_closed := closure_forward_light_cone_subset hq
  have hq0 : 0 ≤ (partial_sum_p n p i) 0 := hq_closed.1
  have h_prod : 0 ≤ coneGap (diff_im n z i hi) * (partial_sum_p n p i) 0 :=
    mul_nonneg (le_of_lt h_gap) hq0
  exact h_prod.trans h_bound

noncomputable def totalConePairing (n : ℕ) (p : Fin n → Fin 4 → ℝ) (z : Fin n → Fin 4 → ℂ) : ℝ :=
  ∑ i : Fin n,
    if hi : i.val + 1 < n then
      minkowskiInner (partial_sum_p n p i) (diff_im n z i hi)
    else 0

lemma totalConePairing_nonneg (n : ℕ) (p : Fin n → Fin 4 → ℝ) (hp : p ∈ spectralRegion n)
    (z : Fin n → Fin 4 → ℂ) (hz : z ∈ forward_tube_n n) :
    0 ≤ totalConePairing n p z := by
  dsimp [totalConePairing]
  apply Finset.sum_nonneg
  intro i _
  split_ifs with hi
  · exact partial_cone_inner_nonneg n p hp z hz i hi
  · rfl

lemma abel_summation_step (n : ℕ) (p : ℕ → ℝ) (v : ℕ → ℝ) :
    (∑ i ∈ Finset.range n, (∑ j ∈ Finset.range (i + 1), p j) * (v i - v (i + 1))) +
      (∑ j ∈ Finset.range (n + 1), p j) * v n =
    ∑ j ∈ Finset.range (n + 1), p j * v j := by
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, zero_add, Finset.range_one,
      Finset.sum_singleton]
  | succ m ih =>
    rw [Finset.sum_range_succ _ m, add_assoc]
    have h_p : (∑ j ∈ Finset.range (m + 2), p j) = (∑ j ∈ Finset.range (m + 1), p j) + p (m + 1) :=
      Finset.sum_range_succ p (m + 1)
    have h_split : (∑ j ∈ Finset.range (m + 1), p j) * (v m - v (m + 1)) +
                   (∑ j ∈ Finset.range (m + 2), p j) * v (m + 1) =
                   (∑ j ∈ Finset.range (m + 1), p j) * v m + p (m + 1) * v (m + 1) := by
      rw [h_p]
      ring
    rw [h_split, ← add_assoc, ih]
    rw [Finset.sum_range_succ _ (m + 1)]

lemma abel_summation_zero_sum (n : ℕ) (p : ℕ → ℝ) (v : ℕ → ℝ)
    (h_sum : ∑ j ∈ Finset.range (n + 1), p j = 0) :
    ∑ i ∈ Finset.range n, (∑ j ∈ Finset.range (i + 1), p j) * (v i - v (i + 1)) =
    ∑ j ∈ Finset.range (n + 1), p j * v j := by
  have h := abel_summation_step n p v
  rw [h_sum, zero_mul, add_zero] at h
  exact h

lemma abel_summation_minkowskiInner (n : ℕ) (p : ℕ → Fin 4 → ℝ) (v : ℕ → Fin 4 → ℝ)
    (h_sum : ∑ j ∈ Finset.range (n + 1), p j = 0) :
    ∑ i ∈ Finset.range n, minkowskiInner (∑ j ∈ Finset.range (i + 1), p j) (v i - v (i + 1)) =
    ∑ j ∈ Finset.range (n + 1), minkowskiInner (p j) (v j) := by
  have h_sum_comp (μ : Fin 4) : ∑ j ∈ Finset.range (n + 1), p j μ = 0 := by
    have h := congr_fun h_sum μ
    rwa [Finset.sum_apply] at h
  simp_rw [minkowskiInner_explicit]
  simp only [Pi.sub_apply]
  have h0 := abel_summation_zero_sum n (fun j => p j 0) (fun j => v j 0) (h_sum_comp 0)
  have h1 := abel_summation_zero_sum n (fun j => p j 1) (fun j => v j 1) (h_sum_comp 1)
  have h2 := abel_summation_zero_sum n (fun j => p j 2) (fun j => v j 2) (h_sum_comp 2)
  have h3 := abel_summation_zero_sum n (fun j => p j 3) (fun j => v j 3) (h_sum_comp 3)
  have h_lhs : (∑ i ∈ Finset.range n,
      ((∑ j ∈ Finset.range (i + 1), p j) 0 * (v i 0 - v (i + 1) 0) -
       (∑ j ∈ Finset.range (i + 1), p j) 1 * (v i 1 - v (i + 1) 1) -
       (∑ j ∈ Finset.range (i + 1), p j) 2 * (v i 2 - v (i + 1) 2) -
       (∑ j ∈ Finset.range (i + 1), p j) 3 * (v i 3 - v (i + 1) 3))) =
      (∑ i ∈ Finset.range n, (∑ j ∈ Finset.range (i + 1), p j) 0 * (v i 0 - v (i + 1) 0)) -
      (∑ i ∈ Finset.range n, (∑ j ∈ Finset.range (i + 1), p j) 1 * (v i 1 - v (i + 1) 1)) -
      (∑ i ∈ Finset.range n, (∑ j ∈ Finset.range (i + 1), p j) 2 * (v i 2 - v (i + 1) 2)) -
      (∑ i ∈ Finset.range n, (∑ j ∈ Finset.range (i + 1), p j) 3 * (v i 3 - v (i + 1) 3)) := by
    repeat rw [Finset.sum_sub_distrib]
  have h_rhs : (∑ j ∈ Finset.range (n + 1),
      (p j 0 * v j 0 - p j 1 * v j 1 - p j 2 * v j 2 - p j 3 * v j 3)) =
      (∑ j ∈ Finset.range (n + 1), p j 0 * v j 0) -
      (∑ j ∈ Finset.range (n + 1), p j 1 * v j 1) -
      (∑ j ∈ Finset.range (n + 1), p j 2 * v j 2) -
      (∑ j ∈ Finset.range (n + 1), p j 3 * v j 3) := by
    repeat rw [Finset.sum_sub_distrib]
  rw [h_lhs, h_rhs]
  simp_rw [Finset.sum_apply]
  rw [h0, h1, h2, h3]

lemma diff_im_eq_sub (n : ℕ) (z : Fin n → Fin 4 → ℂ) (i : Fin n) (hi : i.val + 1 < n) :
    diff_im n z i hi = (fun μ => (z ⟨i.val + 1, hi⟩ μ).im) - (fun μ => (z i μ).im) := by
  ext μ
  simp only [diff_im, diff_z, Complex.sub_im, Pi.sub_apply]
  ring

lemma sub_im_eq_neg_diff_im (n : ℕ) (z : Fin n → Fin 4 → ℂ) (i : Fin n) (hi : i.val + 1 < n) :
    (fun μ => (z i μ).im) - (fun μ => (z ⟨i.val + 1, hi⟩ μ).im) = - diff_im n z i hi := by
  rw [diff_im_eq_sub]
  ext μ
  simp

lemma minkowskiInner_neg_right (u v : Fin 4 → ℝ) :
    minkowskiInner u (- v) = - minkowskiInner u v := by
  simp only [minkowskiInner_explicit, Pi.neg_apply]
  ring

lemma partial_sum_p_eq (n : ℕ) (p : Fin n → Fin 4 → ℝ) (k : Fin n)
    (p_ext : ℕ → Fin 4 → ℝ) (hp : ∀ (j : Fin n), p_ext j.val = p j) :
    partial_sum_p n p k = ∑ j ∈ Finset.range (k.val + 1), p_ext j := by
  dsimp [partial_sum_p]
  rw [← Fin.sum_univ_eq_sum_range]
  have h_le (i : Fin n) (hi : i ∈ Finset.univ.filter (· ≤ k)) : i.val < k.val + 1 := by
    rw [Finset.mem_filter] at hi
    exact Nat.lt_succ_of_le (Fin.le_iff_val_le_val.mp hi.2)
  have h_lt (j : Fin (k.val + 1)) : j.val < n := by
    exact lt_of_le_of_lt (Nat.le_of_lt_succ j.isLt) (Fin.is_lt k)
  apply Finset.sum_bij'
    (fun (i : Fin n) hi => ⟨i.val, h_le i hi⟩)
    (fun (j : Fin (k.val + 1)) _ => ⟨j.val, h_lt j⟩)
    (fun _ _ => Finset.mem_univ _)
    (fun (j : Fin (k.val + 1)) _ => by
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      exact Fin.le_iff_val_le_val.mpr (Nat.le_of_lt_succ j.isLt))
    (fun i hi => by ext; rfl)
    (fun j hj => by ext; rfl)
    (fun i hi => by
      dsimp
      exact (hp i).symm)

lemma totalConePairing_succ (m : ℕ) (p : Fin (m + 1) → Fin 4 → ℝ) (z : Fin (m + 1) → Fin 4 → ℂ) :
    totalConePairing (m + 1) p z =
      ∑ i : Fin m,
        minkowskiInner (partial_sum_p (m + 1) p i.castSucc)
          (diff_im (m + 1) z i.castSucc (Nat.succ_lt_succ i.isLt)) := by
  dsimp [totalConePairing]
  rw [Fin.sum_univ_castSucc]
  have h_last : (if hi : (Fin.last m).val + 1 < m + 1 then
      minkowskiInner (partial_sum_p (m + 1) p (Fin.last m)) (diff_im (m + 1) z (Fin.last m) hi)
    else 0) = 0 := by
    have h_not : ¬ ((Fin.last m).val + 1 < m + 1) := by
      simp only [Fin.val_last, lt_self_iff_false, not_false_eq_true]
    exact dif_neg h_not
  rw [h_last, add_zero]
  apply Finset.sum_congr rfl
  intro i _
  have hi : i.castSucc.val + 1 < m + 1 := by
    simp only [Fin.val_castSucc]
    exact Nat.succ_lt_succ i.isLt
  exact dif_pos hi

lemma sum_minkowskiInner_im_eq_neg_totalConePairing (n : ℕ) (p : Fin n → Fin 4 → ℝ)
    (z : Fin n → Fin 4 → ℂ) (h_sum : ∑ j : Fin n, p j = 0) :
    ∑ j : Fin n, minkowskiInner (p j) (fun μ => (z j μ).im) =
      -totalConePairing n p z := by
  cases n with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.sum_empty, totalConePairing, neg_zero]
  | succ m =>
    let p_ext : ℕ → Fin 4 → ℝ := fun j =>
      if hj : j < m + 1 then p ⟨j, hj⟩ else 0
    let v_ext : ℕ → Fin 4 → ℝ := fun j =>
      if hj : j < m + 1 then (fun μ => (z ⟨j, hj⟩ μ).im) else 0
    have hp_ext (j : Fin (m + 1)) : p_ext j.val = p j := by
      dsimp [p_ext]
      exact dif_pos j.isLt
    have hv_ext (j : Fin (m + 1)) : v_ext j.val = (fun μ => (z j μ).im) := by
      dsimp [v_ext]
      exact dif_pos j.isLt
    have h_sum_ext : ∑ j ∈ Finset.range (m + 1), p_ext j = 0 := by
      rw [← Fin.sum_univ_eq_sum_range]
      have : (∑ i : Fin (m + 1), p_ext i.val) = ∑ i : Fin (m + 1), p i :=
        Finset.sum_congr rfl (fun i _ => hp_ext i)
      rw [this, h_sum]
    have h_abel := abel_summation_minkowskiInner m p_ext v_ext h_sum_ext
    have h_rhs : (∑ j ∈ Finset.range (m + 1), minkowskiInner (p_ext j) (v_ext j)) =
        ∑ j : Fin (m + 1), minkowskiInner (p j) (fun μ => (z j μ).im) := by
      rw [← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro j _
      rw [hp_ext j, hv_ext j]
    rw [h_rhs] at h_abel
    rw [← h_abel]
    rw [totalConePairing_succ]
    rw [← Fin.sum_univ_eq_sum_range]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have hi_lt : i.val < m + 1 := lt_trans i.isLt (Nat.lt_succ_self m)
    have hi1_lt : i.val + 1 < m + 1 := Nat.succ_lt_succ i.isLt
    have h_vi : v_ext i.val = (fun μ => (z ⟨i.val, hi_lt⟩ μ).im) := by
      dsimp [v_ext]; exact dif_pos hi_lt
    have h_vi1 : v_ext (i.val + 1) = (fun μ => (z ⟨i.val + 1, hi1_lt⟩ μ).im) := by
      dsimp [v_ext]; exact dif_pos hi1_lt
    have h_v_sub : v_ext i.val - v_ext (i.val + 1) =
        - diff_im (m + 1) z ⟨i.val, hi_lt⟩ hi1_lt := by
      rw [h_vi, h_vi1]
      exact sub_im_eq_neg_diff_im (m + 1) z ⟨i.val, hi_lt⟩ hi1_lt
    have h_partial : ∑ j ∈ Finset.range (i.val + 1), p_ext j =
        partial_sum_p (m + 1) p i.castSucc := by
      have h_eq := partial_sum_p_eq (m + 1) p i.castSucc p_ext hp_ext
      rw [Fin.val_castSucc] at h_eq
      exact h_eq.symm
    rw [h_partial, h_v_sub, minkowskiInner_neg_right]
    rfl

def ge_filter (m : ℕ) (i : ℕ) : Finset (Fin m) :=
  Finset.univ.filter (fun j => i ≤ j.val)

def diff_to_full (m : ℕ) (xi : Fin m → Fin 4 → ℝ) (x_last : Fin 4 → ℝ) :
    Fin (m + 1) → Fin 4 → ℝ := fun i =>
  (∑ j ∈ ge_filter m i.val, xi j) + x_last

def full_to_diff (m : ℕ) (x : Fin (m + 1) → Fin 4 → ℝ) :
    (Fin m → Fin 4 → ℝ) × (Fin 4 → ℝ) :=
  (fun k => x (Fin.castSucc k) - x (Fin.succ k), x (Fin.last m))

lemma ge_filter_last (m : ℕ) : ge_filter m m = ∅ := by
  apply Finset.filter_false_of_mem
  intro j _
  exact not_le_of_gt j.isLt

lemma ge_filter_succ (m : ℕ) (k : Fin m) :
    ge_filter m k.val = insert k (ge_filter m (k.val + 1)) := by
  ext j
  simp only [ge_filter, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
  constructor
  · intro hj
    by_cases heq : j = k
    · exact Or.inl heq
    · right
      have hne : k.val ≠ j.val := fun h => heq (Fin.ext h.symm)
      exact Nat.succ_le_of_lt (lt_of_le_of_ne hj hne)
  · rintro (rfl | hj)
    · exact le_rfl
    · exact le_trans (Nat.le_succ k.val) hj

lemma not_mem_ge_filter_succ (m : ℕ) (k : Fin m) :
    k ∉ ge_filter m (k.val + 1) := by
  simp only [ge_filter, Finset.mem_filter, Finset.mem_univ, true_and]
  exact Nat.not_succ_le_self k.val

lemma full_to_diff_to_full (m : ℕ) (xi : Fin m → Fin 4 → ℝ) (x_last : Fin 4 → ℝ) :
    full_to_diff m (diff_to_full m xi x_last) = (xi, x_last) := by
  refine Prod.ext ?_ ?_
  · ext k μ
    dsimp [full_to_diff, diff_to_full]
    rw [ge_filter_succ m k]
    rw [Finset.sum_insert (not_mem_ge_filter_succ m k)]
    simp
  · ext μ
    dsimp [full_to_diff, diff_to_full]
    rw [ge_filter_last m, Finset.sum_empty]
    simp

lemma diff_to_full_to_diff_val (m : ℕ) (x : Fin (m + 1) → Fin 4 → ℝ) (d : ℕ) (hd : d ≤ m) :
    diff_to_full m (full_to_diff m x).1 (full_to_diff m x).2 ⟨m - d, by omega⟩ =
    x ⟨m - d, by omega⟩ := by
  induction d with
  | zero =>
    dsimp [diff_to_full, full_to_diff]
    rw [ge_filter_last m, Finset.sum_empty]
    ext μ
    simp only [zero_add]
    have h_last : (Fin.last m) = (⟨m, by omega⟩ : Fin (m + 1)) := rfl
    rw [h_last]
  | succ d ih =>
    have hd_lt : d < m := Nat.lt_of_succ_le hd
    have h_step : m - (d + 1) + 1 = m - d := by omega
    let k : Fin m := ⟨m - (d + 1), by omega⟩
    have hk_val : k.val = m - (d + 1) := rfl
    have ih' := ih (by omega)
    dsimp [diff_to_full, full_to_diff] at ih' ⊢
    rw [ge_filter_succ m k]
    rw [Finset.sum_insert (not_mem_ge_filter_succ m k)]
    simp only [hk_val]
    rw [h_step]
    have h_assoc : (x k.castSucc - x k.succ) +
        (∑ j ∈ ge_filter m (m - d), (x j.castSucc - x j.succ)) + x (Fin.last m) =
        (x k.castSucc - x k.succ) +
        ((∑ j ∈ ge_filter m (m - d), (x j.castSucc - x j.succ)) + x (Fin.last m)) := by
      ext μ; simp; ring
    rw [h_assoc, ih']
    have h_succ_eq : k.succ = (⟨m - d, by omega⟩ : Fin (m + 1)) := by
      ext; simp [hk_val, h_step]
    rw [h_succ_eq]
    ext μ
    simp only [Pi.add_apply, Pi.sub_apply]
    have h_kcast : k.castSucc = (⟨m - (d + 1), by omega⟩ : Fin (m + 1)) := by
      ext; exact hk_val
    rw [h_kcast]
    ring

lemma diff_to_full_to_diff (m : ℕ) (x : Fin (m + 1) → Fin 4 → ℝ) :
    diff_to_full m (full_to_diff m x).1 (full_to_diff m x).2 = x := by
  ext i μ
  have hi_le : m - i.val ≤ m := by omega
  have h_val := congr_fun (diff_to_full_to_diff_val m x (m - i.val) hi_le) μ
  have h_sub : m - (m - i.val) = i.val := Nat.sub_sub_self (Nat.le_of_lt_succ i.isLt)
  have h_idx : (⟨m - (m - i.val), by omega⟩ : Fin (m + 1)) = i := by
    ext
    exact h_sub
  rw [h_idx] at h_val
  exact h_val

lemma full_to_diff_lorentz (m : ℕ) (A : SL2C) (x : Fin (m + 1) → Fin 4 → ℝ) :
    full_to_diff m (fun i => (lorentzOfSL2C A).mulVec (x i)) =
    (fun k => (lorentzOfSL2C A).mulVec ((full_to_diff m x).1 k),
     (lorentzOfSL2C A).mulVec ((full_to_diff m x).2)) := by
  refine Prod.ext ?_ ?_
  · ext k μ
    dsimp [full_to_diff]
    rw [Matrix.mulVec_sub]
    rfl
  · rfl

lemma diff_to_full_lorentz (m : ℕ) (A : SL2C) (xi : Fin m → Fin 4 → ℝ) (x_last : Fin 4 → ℝ) :
    diff_to_full m (fun k => (lorentzOfSL2C A).mulVec (xi k)) ((lorentzOfSL2C A).mulVec x_last) =
    fun i => (lorentzOfSL2C A).mulVec (diff_to_full m xi x_last i) := by
  ext i μ
  dsimp [diff_to_full]
  rw [Matrix.mulVec_add, Matrix.mulVec_sum]
  rfl

def diffCoordLinearEquiv (m : ℕ) :
    (Fin (m + 1) → Fin 4 → ℝ) ≃ₗ[ℝ] (Fin m → Fin 4 → ℝ) × (Fin 4 → ℝ) where
  toFun := full_to_diff m
  invFun p := diff_to_full m p.1 p.2
  left_inv x := diff_to_full_to_diff m x
  right_inv p := full_to_diff_to_full m p.1 p.2
  map_add' x y := by
    refine Prod.ext ?_ ?_
    · ext k μ
      dsimp [full_to_diff]
      ring
    · ext μ
      rfl
  map_smul' c x := by
    refine Prod.ext ?_ ?_
    · ext k μ
      dsimp [full_to_diff]
      ring
    · ext μ
      rfl

noncomputable def diffCoordCLE (m : ℕ) :
    (Fin (m + 1) → Fin 4 → ℝ) ≃L[ℝ] (Fin m → Fin 4 → ℝ) × (Fin 4 → ℝ) :=
  LinearEquiv.toContinuousLinearEquiv (diffCoordLinearEquiv m)

lemma diffCoordLinearEquiv_lorentz (m : ℕ) (A : SL2C) (x : Fin (m + 1) → Fin 4 → ℝ) :
    diffCoordLinearEquiv m ((lorentzEquiv (m + 1) A) x) =
      ((lorentzEquiv m A) (diffCoordLinearEquiv m x).1,
       (lorentzOfSL2C A).mulVec (diffCoordLinearEquiv m x).2) := by
  dsimp [diffCoordLinearEquiv, lorentzEquiv, lorentzActLM]
  have h := full_to_diff_lorentz m A x
  exact h

lemma diffCoordLinearEquiv_symm_apply (m : ℕ) (xi : Fin m → Fin 4 → ℝ) (x_last : Fin 4 → ℝ) :
    (diffCoordLinearEquiv m).symm (xi, x_last) = diff_to_full m xi x_last := rfl

lemma diffCoordLinearEquiv_symm_lorentz (m : ℕ) (A : SL2C)
    (xi : Fin m → Fin 4 → ℝ) (x_last : Fin 4 → ℝ) :
    (diffCoordLinearEquiv m).symm
        ((lorentzEquiv m A) xi, (lorentzOfSL2C A).mulVec x_last) =
      (lorentzEquiv (m + 1) A) ((diffCoordLinearEquiv m).symm (xi, x_last)) := by
  dsimp [diffCoordLinearEquiv, lorentzEquiv, lorentzActLM]
  have h := diff_to_full_lorentz m A xi x_last
  exact h

lemma sum_minkowskiInner_eq_diff (m : ℕ) (p : Fin (m + 1) → Fin 4 → ℝ)
    (x : Fin (m + 1) → Fin 4 → ℝ) (h_sum : ∑ j : Fin (m + 1), p j = 0) :
    ∑ j : Fin (m + 1), minkowskiInner (p j) (x j) =
      ∑ k : Fin m,
        minkowskiInner (partial_sum_p (m + 1) p k.castSucc) ((full_to_diff m x).1 k) := by
  let p_ext : ℕ → Fin 4 → ℝ := fun j =>
    if hj : j < m + 1 then p ⟨j, hj⟩ else 0
  let v_ext : ℕ → Fin 4 → ℝ := fun j =>
    if hj : j < m + 1 then x ⟨j, hj⟩ else 0
  have hp_ext (j : Fin (m + 1)) : p_ext j.val = p j := by
    dsimp [p_ext]
    exact dif_pos j.isLt
  have hv_ext (j : Fin (m + 1)) : v_ext j.val = x j := by
    dsimp [v_ext]
    exact dif_pos j.isLt
  have h_sum_ext : ∑ j ∈ Finset.range (m + 1), p_ext j = 0 := by
    rw [← Fin.sum_univ_eq_sum_range]
    have : (∑ i : Fin (m + 1), p_ext i.val) = ∑ i : Fin (m + 1), p i :=
      Finset.sum_congr rfl (fun i _ => hp_ext i)
    rw [this, h_sum]
  have h_abel := abel_summation_minkowskiInner m p_ext v_ext h_sum_ext
  have h_rhs : (∑ j ∈ Finset.range (m + 1), minkowskiInner (p_ext j) (v_ext j)) =
      ∑ j : Fin (m + 1), minkowskiInner (p j) (x j) := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j _
    rw [hp_ext j, hv_ext j]
  rw [h_rhs] at h_abel
  rw [← h_abel]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  have hi_lt : i.val < m + 1 := lt_trans i.isLt (Nat.lt_succ_self m)
  have hi1_lt : i.val + 1 < m + 1 := Nat.succ_lt_succ i.isLt
  have h_vi : v_ext i.val = x ⟨i.val, hi_lt⟩ := by
    dsimp [v_ext]; exact dif_pos hi_lt
  have h_vi1 : v_ext (i.val + 1) = x ⟨i.val + 1, hi1_lt⟩ := by
    dsimp [v_ext]; exact dif_pos hi1_lt
  have h_v_sub : v_ext i.val - v_ext (i.val + 1) = (full_to_diff m x).1 i := by
    rw [h_vi, h_vi1]
    dsimp [full_to_diff]
    rfl
  have h_partial : ∑ j ∈ Finset.range (i.val + 1), p_ext j =
      partial_sum_p (m + 1) p i.castSucc := by
    have h_eq := partial_sum_p_eq (m + 1) p i.castSucc p_ext hp_ext
    rw [Fin.val_castSucc] at h_eq
    exact h_eq.symm
  rw [h_partial, h_v_sub]

lemma sum_minkowskiInner_diff_to_full (m : ℕ) (p : Fin (m + 1) → Fin 4 → ℝ)
    (xi : Fin m → Fin 4 → ℝ) (x_last : Fin 4 → ℝ) (h_sum : ∑ j : Fin (m + 1), p j = 0) :
    ∑ j : Fin (m + 1), minkowskiInner (p j) (diff_to_full m xi x_last j) =
      ∑ k : Fin m, minkowskiInner (partial_sum_p (m + 1) p k.castSucc) (xi k) := by
  have h := sum_minkowskiInner_eq_diff m p (diff_to_full m xi x_last) h_sum
  have h_full : full_to_diff m (diff_to_full m xi x_last) = (xi, x_last) :=
    full_to_diff_to_full m xi x_last
  rw [h_full] at h
  exact h

def total_momentum_LM (n : ℕ) : (Fin n → Fin 4 → ℝ) →ₗ[ℝ] (Fin 4 → ℝ) where
  toFun p := ∑ i : Fin n, p i
  map_add' x y := by
    simp only [Pi.add_apply]
    exact Finset.sum_add_distrib
  map_smul' c x := by
    simp only [Pi.smul_apply, RingHom.id_apply]
    rw [Finset.smul_sum]

noncomputable def total_momentum_CLM (n : ℕ) : (Fin n → Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ) :=
  LinearMap.toContinuousLinearMap (total_momentum_LM n)

lemma total_momentum_lorentz (n : ℕ) (A : SL2C) (p : Fin n → Fin 4 → ℝ) :
    total_momentum_LM n (lorentzEquiv n A p) =
      (lorentzOfSL2C A).mulVec (total_momentum_LM n p) := by
  dsimp [total_momentum_LM, lorentzEquiv, lorentzActLM]
  rw [Matrix.mulVec_sum]

lemma total_momentum_eq_zero_of_mem_spectralRegion (n : ℕ) (p : Fin n → Fin 4 → ℝ)
    (hp : p ∈ spectralRegion n) :
    total_momentum_LM n p = 0 :=
  hp.1

lemma total_momentum_lorentz_eq_zero (n : ℕ) (A : SL2C) (p : Fin n → Fin 4 → ℝ)
    (hp : p ∈ spectralRegion n) :
    total_momentum_LM n (lorentzEquiv n A p) = 0 := by
  rw [total_momentum_lorentz, total_momentum_eq_zero_of_mem_spectralRegion n p hp]
  exact Matrix.mulVec_zero (lorentzOfSL2C A)

lemma total_momentum_preimage_isOpen (n : ℕ) (V : Set (Fin 4 → ℝ)) (hV : IsOpen V) :
    IsOpen ((total_momentum_CLM n) ⁻¹' V) :=
  (total_momentum_CLM n).continuous.isOpen_preimage V hV

lemma spectralRegion_subset_total_momentum_preimage (n : ℕ) (V : Set (Fin 4 → ℝ)) (h0 : 0 ∈ V) :
    spectralRegion n ⊆ (total_momentum_CLM n) ⁻¹' V := by
  intro p hp
  simp only [Set.mem_preimage]
  have h_zero : total_momentum_CLM n p = 0 := total_momentum_eq_zero_of_mem_spectralRegion n p hp
  rw [h_zero]
  exact h0

def comNeighborhood (n : ℕ) (A : SL2C) (R : ℝ) : Set (Fin n → Fin 4 → ℝ) :=
  { p | total_momentum_LM n p ∈ Metric.ball (0 : Fin 4 → ℝ) R ∧
        (lorentzOfSL2C A⁻¹).mulVec (total_momentum_LM n p) ∈ Metric.ball (0 : Fin 4 → ℝ) R ∧
        p ∈ Metric.ball (0 : Fin n → Fin 4 → ℝ) R ∧
        (lorentzEquiv n A⁻¹) p ∈ Metric.ball (0 : Fin n → Fin 4 → ℝ) R }

lemma isOpen_comNeighborhood (n : ℕ) (A : SL2C) (R : ℝ) :
    IsOpen (comNeighborhood n A R) := by
  have h1 : IsOpen { p : Fin n → Fin 4 → ℝ |
      total_momentum_LM n p ∈ Metric.ball (0 : Fin 4 → ℝ) R } :=
    Metric.isOpen_ball.preimage (total_momentum_CLM n).continuous
  have h2 : IsOpen { p : Fin n → Fin 4 → ℝ |
      (lorentzOfSL2C A⁻¹).mulVec (total_momentum_LM n p) ∈ Metric.ball (0 : Fin 4 → ℝ) R } := by
    have h_cont2 : Continuous (fun p => (lorentzOfSL2C A⁻¹).mulVec (total_momentum_LM n p)) := by
      change Continuous ((Matrix.toLin' (lorentzOfSL2C A⁻¹)).toContinuousLinearMap.comp
        (total_momentum_CLM n))
      exact ContinuousLinearMap.continuous _
    exact Metric.isOpen_ball.preimage h_cont2
  have h3 : IsOpen { p : Fin n → Fin 4 → ℝ | p ∈ Metric.ball (0 : Fin n → Fin 4 → ℝ) R } :=
    Metric.isOpen_ball
  have h4 : IsOpen { p : Fin n → Fin 4 → ℝ |
      (lorentzEquiv n A⁻¹) p ∈ Metric.ball (0 : Fin n → Fin 4 → ℝ) R } :=
    Metric.isOpen_ball.preimage (lorentzEquiv n A⁻¹).continuous
  exact h1.inter (h2.inter (h3.inter h4))

lemma spectralRegion_subset_comNeighborhood (n : ℕ) (A : SL2C) (R : ℝ) (hR : 0 < R) :
    spectralRegion n ⊆ comNeighborhood n A R := by
  intro p hp
  have hp0 : p = 0 := hp.2.2
  subst hp0
  have hs0 : total_momentum_LM n 0 = 0 := map_zero _
  have hl0 : (lorentzEquiv n A⁻¹) 0 = 0 := map_zero _
  refine ⟨?_, ?_, Metric.mem_ball_self hR, ?_⟩
  · rw [hs0]
    exact Metric.mem_ball_self hR
  · rw [hs0, Matrix.mulVec_zero]
    exact Metric.mem_ball_self hR
  · rw [hl0]
    exact Metric.mem_ball_self hR

def comCutoffBump (R : ℝ) (hR : 0 < R) : ContDiffBump (0 : Fin 4 → ℝ) where
  rIn := R
  rOut := 2 * R
  rIn_pos := hR
  rIn_lt_rOut := by linarith

noncomputable def comCutoff (n : ℕ) (R : ℝ) (hR : 0 < R)
    (p : Fin n → Fin 4 → ℝ) : ℝ :=
  comCutoffBump R hR (total_momentum_LM n p)

lemma comCutoff_lorentz_eq_one (n : ℕ) (A : SL2C) (R : ℝ) (hR : 0 < R)
    (p : Fin n → Fin 4 → ℝ) (hp : p ∈ comNeighborhood n A R) :
    comCutoff n R hR p = 1 ∧
    comCutoff n R hR ((lorentzEquiv n A⁻¹) p) = 1 := by
  obtain ⟨h1, h2, _, _⟩ := hp
  dsimp [comCutoff]
  have h_com1 : (comCutoffBump R hR) (total_momentum_LM n p) = 1 := by
    apply (comCutoffBump R hR).one_of_mem_closedBall
    exact Metric.ball_subset_closedBall h1
  have h_com2 : (comCutoffBump R hR) (total_momentum_LM n ((lorentzEquiv n A⁻¹) p)) = 1 := by
    rw [total_momentum_lorentz]
    apply (comCutoffBump R hR).one_of_mem_closedBall
    exact Metric.ball_subset_closedBall h2
  exact ⟨h_com1, h_com2⟩

lemma mul_re_im (a : ℝ) (b : ℂ) :
    (a : ℂ) * b = (a * b.re : ℂ) + Complex.I * (a * b.im : ℂ) := by
  apply Complex.ext <;> simp

lemma minkowskiInnerC_coe_real (p : Fin 4 → ℝ) (z : Fin 4 → ℂ) :
    minkowskiInnerC (fun μ => (p μ : ℂ)) z =
      (minkowskiInner p (fun μ => (z μ).re) : ℂ) +
      Complex.I * (minkowskiInner p (fun μ => (z μ).im) : ℂ) := by
  dsimp [minkowskiInnerC]
  rw [minkowskiInner_explicit, minkowskiInner_explicit]
  rw [mul_re_im (p 0) (z 0), mul_re_im (p 1) (z 1), mul_re_im (p 2) (z 2), mul_re_im (p 3) (z 3)]
  push_cast
  ring

lemma neg_I_mul_minkowskiInnerC_re (p : Fin 4 → ℝ) (z : Fin 4 → ℂ) :
    (- Complex.I * minkowskiInnerC (fun μ => (p μ : ℂ)) z).re =
      minkowskiInner p (fun μ => (z μ).im) := by
  rw [minkowskiInnerC_coe_real]
  have h_mul : - Complex.I * ((minkowskiInner p (fun μ => (z μ).re) : ℂ) +
      Complex.I * (minkowskiInner p (fun μ => (z μ).im) : ℂ)) =
    (minkowskiInner p (fun μ => (z μ).im) : ℂ) -
      Complex.I * (minkowskiInner p (fun μ => (z μ).re) : ℂ) := by
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [h_mul]
  simp

lemma norm_exp_neg_I_minkowskiInnerC (p : Fin 4 → ℝ) (z : Fin 4 → ℂ) :
    ‖Complex.exp (- Complex.I * minkowskiInnerC (fun μ => (p μ : ℂ)) z)‖ =
      Real.exp (minkowskiInner p (fun μ => (z μ).im)) := by
  rw [Complex.norm_exp, neg_I_mul_minkowskiInnerC_re]

lemma sum_neg_I_mul_minkowskiInnerC_re (n : ℕ) (p : Fin n → Fin 4 → ℝ) (z : Fin n → Fin 4 → ℂ) :
    (- Complex.I * (∑ k : Fin n, minkowskiInnerC (fun μ => (p k μ : ℂ)) (z k))).re =
      ∑ k : Fin n, minkowskiInner (p k) (fun μ => (z k μ).im) := by
  have h1 : - Complex.I * (∑ k : Fin n, minkowskiInnerC (fun μ => (p k μ : ℂ)) (z k)) =
      ∑ k : Fin n, (- Complex.I * minkowskiInnerC (fun μ => (p k μ : ℂ)) (z k)) := by
    rw [Finset.mul_sum]
  rw [h1, Complex.re_sum]
  exact Finset.sum_congr rfl (fun k _ => neg_I_mul_minkowskiInnerC_re (p k) (z k))

lemma norm_exp_sum_neg_I_minkowskiInnerC (n : ℕ) (p : Fin n → Fin 4 → ℝ) (z : Fin n → Fin 4 → ℂ) :
    ‖Complex.exp (- Complex.I * (∑ k : Fin n, minkowskiInnerC (fun μ => (p k μ : ℂ)) (z k)))‖ =
      Real.exp (∑ k : Fin n, minkowskiInner (p k) (fun μ => (z k μ).im)) := by
  rw [Complex.norm_exp, sum_neg_I_mul_minkowskiInnerC_re]

lemma norm_exp_sum_neg_I_minkowskiInnerC_spectral (n : ℕ) (p : Fin n → Fin 4 → ℝ)
    (hp : p ∈ spectralRegion n) (z : Fin n → Fin 4 → ℂ) (hz : z ∈ forward_tube_n n) :
    ‖Complex.exp (- Complex.I *
      (∑ k : Fin n, minkowskiInnerC (fun μ => (p k μ : ℂ)) (z k)))‖ ≤ 1 := by
  rw [norm_exp_sum_neg_I_minkowskiInnerC]
  rw [sum_minkowskiInner_im_eq_neg_totalConePairing n p z hp.1]
  have h_pair := totalConePairing_nonneg n p hp z hz
  have h_le_zero : -totalConePairing n p z ≤ 0 := by linarith
  have h_exp := Real.exp_le_exp_of_le h_le_zero
  rw [Real.exp_zero] at h_exp
  exact h_exp

lemma add_I_mul_im (a b : ℝ) : ((a : ℂ) + Complex.I * (b : ℂ)).im = b := by
  simp

lemma forward_light_cone_smul (t : ℝ) (ht : 0 < t) (v : Fin 4 → ℝ) (hv : v ∈ forward_light_cone) :
    t • v ∈ forward_light_cone := by
  have hv0 : 0 < v 0 := hv.1
  have hvv : 0 < minkowskiInner v v := hv.2
  refine ⟨by simp [mul_pos ht hv0], ?_⟩
  rw [minkowskiInner_explicit] at hvv ⊢
  simp only [Pi.smul_apply, smul_eq_mul]
  have h_sq : (t * v 0) * (t * v 0) - (t * v 1) * (t * v 1) - (t * v 2) * (t * v 2) -
      (t * v 3) * (t * v 3) = t^2 * (v 0 * v 0 - v 1 * v 1 - v 2 * v 2 - v 3 * v 3) := by ring
  rw [h_sq]
  have ht2 : 0 < t^2 := sq_pos_of_ne_zero (ne_of_gt ht)
  exact mul_pos ht2 hvv

lemma line_mem_forward_tube (n : ℕ) (x : Fin n → Fin 4 → ℝ) (v : Fin 4 → ℝ)
    (hv : v ∈ forward_light_cone) (t : ℝ) (ht : 0 < t) :
    (fun (i : Fin n) (k : Fin 4) => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ)) ∈
      forward_tube_n n := by
  intro i hi
  have h_im : (fun k => -((((x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ)) -
      ((x ⟨i.val + 1, hi⟩ k : ℂ) + Complex.I * ((t * ((i.val + 1 : ℕ) : ℝ) * v k : ℝ) : ℂ))).im)) =
      t • v := by
    ext k
    simp only [Complex.sub_im, add_I_mul_im, Pi.smul_apply, smul_eq_mul]
    push_cast
    ring
  change (fun k => -((((x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ)) -
      ((x ⟨i.val + 1, hi⟩ k : ℂ) + Complex.I * ((t * ((i.val + 1 : ℕ) : ℝ) * v k : ℝ) : ℂ))).im)) ∈
      forward_light_cone
  rw [h_im]
  exact forward_light_cone_smul t ht v hv

lemma complex_lorentz_preserves_inner_pair (Λ : SpecialSpecialComplexLorentzGroup)
    (z w : Fin 4 → ℂ) :
    minkowskiInnerC (Λ • z) (Λ • w) = minkowskiInnerC z w := by
  rw [minkowskiInnerC_eq_alt, minkowskiInnerC_eq_alt]
  dsimp [minkowskiInnerC_alt]
  have h_lorentz : (Matrix.transpose Λ.val.val) * minkowskiMetric * (Λ.val.val) = minkowskiMetric :=
    Λ.property.1
  have h1 : dotProduct (Λ • z) (minkowskiMetric.mulVec (Λ • w)) =
            dotProduct z (((Matrix.transpose Λ.val.val) * minkowskiMetric *
              (Λ.val.val)).mulVec w) := by
    change dotProduct ((Λ.val.val).mulVec z) (minkowskiMetric.mulVec ((Λ.val.val).mulVec w)) = _
    rw [dotProduct_mulVec_left, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  rw [h1, h_lorentz]

noncomputable def vladimirov_kernel (n : ℕ) (z : Fin n → Fin 4 → ℂ) (p : Fin n → Fin 4 → ℝ) : ℂ :=
  Complex.exp (- Complex.I * (∑ k : Fin n, minkowskiInnerC (fun μ => (p k μ : ℂ)) (z k)))

lemma vladimirov_kernel_norm (n : ℕ) (z : Fin n → Fin 4 → ℂ) (p : Fin n → Fin 4 → ℝ) :
    ‖vladimirov_kernel n z p‖ =
      Real.exp (∑ k : Fin n, minkowskiInner (p k) (fun μ => (z k μ).im)) := by
  dsimp [vladimirov_kernel]
  exact norm_exp_sum_neg_I_minkowskiInnerC n p z

lemma vladimirov_kernel_norm_le_one_of_spectralRegion (n : ℕ) (p : Fin n → Fin 4 → ℝ)
    (hp : p ∈ spectralRegion n) (z : Fin n → Fin 4 → ℂ) (hz : z ∈ forward_tube_n n) :
    ‖vladimirov_kernel n z p‖ ≤ 1 := by
  rw [vladimirov_kernel_norm]
  have h_sum : ∑ j : Fin n, p j = 0 := hp.1
  rw [sum_minkowskiInner_im_eq_neg_totalConePairing n p z h_sum]
  have h_pair := totalConePairing_nonneg n p hp z hz
  have h_neg : - totalConePairing n p z ≤ 0 := by linarith
  exact Real.exp_le_one_iff.mpr h_neg

lemma lorentzOfSL2C_mulVec_coe (A : SL2C) (p : Fin 4 → ℝ) :
    (fun μ => ((lorentzOfSL2C A).mulVec p μ : ℂ)) =
      (spinorPhi (A, sl2c_conj A)) • (fun μ => (p μ : ℂ)) := by
  ext μ
  have h_map := (lorentzOfSL2C_map A).symm
  change ((lorentzOfSL2C A).mulVec p μ : ℂ) =
    ((spinorPhi (A, sl2c_conj A)).val.val.mulVec (fun ν => (p ν : ℂ))) μ
  rw [h_map]
  dsimp [Matrix.mulVec, dotProduct]
  push_cast
  rfl

lemma vladimirov_kernel_lorentz (n : ℕ) (A : SL2C)
    (z : Fin n → Fin 4 → ℂ) (p : Fin n → Fin 4 → ℝ) :
    vladimirov_kernel n (spinorPhi (A, sl2c_conj A) • z)
      (fun k => (lorentzOfSL2C A).mulVec (p k)) =
    vladimirov_kernel n z p := by
  dsimp [vladimirov_kernel]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [lorentzOfSL2C_mulVec_coe A (p k)]
  exact complex_lorentz_preserves_inner_pair (spinorPhi (A, sl2c_conj A))
    (fun μ => (p k μ : ℂ)) (z k)

lemma minkowskiInner_lorentz (A : SL2C) (p q : Fin 4 → ℝ) :
    minkowskiInner ((lorentzOfSL2C A).mulVec p) ((lorentzOfSL2C A).mulVec q) =
    minkowskiInner p q := by
  have h_c : minkowskiInnerC (fun μ => (((lorentzOfSL2C A).mulVec p) μ : ℂ))
                             (fun μ => (((lorentzOfSL2C A).mulVec q) μ : ℂ)) =
             minkowskiInnerC (fun μ => (p μ : ℂ)) (fun μ => (q μ : ℂ)) := by
    rw [lorentzOfSL2C_mulVec_coe, lorentzOfSL2C_mulVec_coe]
    exact complex_lorentz_preserves_inner_pair (spinorPhi (A, sl2c_conj A)) _ _
  have h_re1 : (minkowskiInnerC (fun μ => (((lorentzOfSL2C A).mulVec p) μ : ℂ))
                                (fun μ => (((lorentzOfSL2C A).mulVec q) μ : ℂ))).re =
               minkowskiInner ((lorentzOfSL2C A).mulVec p) ((lorentzOfSL2C A).mulVec q) := by
    rw [minkowskiInnerC_coe_real]
    simp
  have h_re2 : (minkowskiInnerC (fun μ => (p μ : ℂ)) (fun μ => (q μ : ℂ))).re =
               minkowskiInner p q := by
    rw [minkowskiInnerC_coe_real]
    simp
  rw [← h_re1, ← h_re2, h_c]

lemma minkowskiInner_lorentz_pair (A : SL2C) (p x : Fin 4 → ℝ) :
    minkowskiInner p ((lorentzOfSL2C A).mulVec x) =
    minkowskiInner ((lorentzOfSL2C A⁻¹).mulVec p) x := by
  have h := (minkowskiInner_lorentz A⁻¹ p ((lorentzOfSL2C A).mulVec x)).symm
  rw [h]
  have h_mul : (lorentzOfSL2C A⁻¹).mulVec ((lorentzOfSL2C A).mulVec x) = x := by
    rw [Matrix.mulVec_mulVec, ← lorentzOfSL2C_mul, inv_mul_cancel]
    rw [lorentzOfSL2C_one, Matrix.one_mulVec]
  rw [h_mul]

lemma sum_minkowskiInner_lorentz_pair (n : ℕ) (A : SL2C)
    (p : Fin n → Fin 4 → ℝ) (x : Fin n → Fin 4 → ℝ) :
    (∑ k : Fin n, minkowskiInner (p k) ((lorentzOfSL2C A).mulVec (x k))) =
    (∑ k : Fin n, minkowskiInner ((lorentzOfSL2C A⁻¹).mulVec (p k)) (x k)) := by
  apply Finset.sum_congr rfl
  intro k _
  exact minkowskiInner_lorentz_pair A (p k) (x k)

lemma minkowskiInner_smul_right (x y : Fin 4 → ℝ) (c : ℝ) :
    minkowskiInner x (c • y) = c * minkowskiInner x y := by
  simp only [minkowskiInner_explicit, Pi.smul_apply, smul_eq_mul]
  ring

lemma minkowskiInner_smul_left (x y : Fin 4 → ℝ) (c : ℝ) :
    minkowskiInner (c • x) y = c * minkowskiInner x y := by
  simp only [minkowskiInner_explicit, Pi.smul_apply, smul_eq_mul]
  ring

lemma line_im_eq (t : ℝ) (v : Fin 4 → ℝ) (k : ℕ) :
    (fun μ => (((k : ℝ) * (t * v μ) : ℝ))) = (t * (k : ℝ)) • v := by
  ext μ
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

lemma minkowskiInner_line_im (n : ℕ) (p : Fin n → Fin 4 → ℝ) (v : Fin 4 → ℝ)
    (t : ℝ) (k : Fin n) :
    minkowskiInner (p k) (fun μ => (((t * ((k : ℕ) : ℝ) * v μ : ℝ)))) =
      (t * ((k : ℕ) : ℝ)) * minkowskiInner (p k) v := by
  have h_im : (fun μ => (((t * ((k : ℕ) : ℝ) * v μ : ℝ)))) = (t * ((k : ℕ) : ℝ)) • v := by
    ext μ
    simp only [Pi.smul_apply, smul_eq_mul]
  rw [h_im, minkowskiInner_smul_right]

lemma sum_minkowskiInner_line_im (n : ℕ) (p : Fin n → Fin 4 → ℝ) (v : Fin 4 → ℝ) (t : ℝ) :
    (∑ k : Fin n, minkowskiInner (p k) (fun μ => (((t * ((k : ℕ) : ℝ) * v μ : ℝ))))) =
      t * ∑ k : Fin n, ((k : ℕ) : ℝ) * minkowskiInner (p k) v := by
  simp_rw [minkowskiInner_line_im, mul_assoc]
  exact (Finset.mul_sum (Finset.univ : Finset (Fin n)) _ t).symm

lemma vladimirov_kernel_line_norm (n : ℕ) (p : Fin n → Fin 4 → ℝ) (x : Fin n → Fin 4 → ℝ)
    (v : Fin 4 → ℝ) (t : ℝ) :
    ‖vladimirov_kernel n
        (fun i k => (x i k : ℂ) + Complex.I * ((t * ((i : ℕ) : ℝ) * v k : ℝ) : ℂ)) p‖ =
      Real.exp (t * ∑ k : Fin n, ((k : ℕ) : ℝ) * minkowskiInner (p k) v) := by
  rw [vladimirov_kernel_norm]
  congr 1
  have h_sum : (∑ k : Fin n, minkowskiInner (p k)
      (fun μ => ((x k μ : ℂ) + Complex.I * ((t * ((k : ℕ) : ℝ) * v μ : ℝ) : ℂ)).im)) =
      (∑ k : Fin n, minkowskiInner (p k) (fun μ => (t * ((k : ℕ) : ℝ) * v μ : ℝ))) := by
    apply Finset.sum_congr rfl
    intro k _
    have h_im : (fun μ => ((x k μ : ℂ) + Complex.I * ((t * ((k : ℕ) : ℝ) * v μ : ℝ) : ℂ)).im) =
        (fun μ => (t * ((k : ℕ) : ℝ) * v μ : ℝ)) := by
      ext μ
      exact add_I_mul_im (x k μ) (t * ((k : ℕ) : ℝ) * v μ)
    rw [h_im]
  rw [h_sum, sum_minkowskiInner_line_im]

lemma double_sum_triangle (n : ℕ) (a : Fin n → ℝ) :
    (∑ k : Fin n, ∑ _j ∈ Finset.univ.filter (· < k), a k) =
      ∑ j : Fin n, ∑ k ∈ Finset.univ.filter (fun k => j < k), a k := by
  have h1 : (∑ k : Fin n, ∑ _j ∈ Finset.univ.filter (· < k), a k) =
      ∑ k : Fin n, ∑ j : Fin n, if j < k then a k else 0 := by
    apply Finset.sum_congr rfl
    intro k _
    rw [← Finset.sum_filter]
  have h2 : (∑ j : Fin n, ∑ k ∈ Finset.univ.filter (fun k => j < k), a k) =
      ∑ j : Fin n, ∑ k : Fin n, if j < k then a k else 0 := by
    apply Finset.sum_congr rfl
    intro _ _
    rw [← Finset.sum_filter]
  rw [h1, h2, Finset.sum_comm]

lemma sum_filter_lt_const (n : ℕ) (k : Fin n) (c : ℝ) :
    (∑ _j ∈ Finset.univ.filter (· < k), c) = ((k : ℕ) : ℝ) * c := by
  rw [Finset.sum_const, nsmul_eq_mul]
  have h : (Finset.univ.filter (· < k)).card = k.val := by
    have h1 := Fin.card_filter_val_lt (n := n) (m := k.val)
    rwa [Nat.min_eq_right (le_of_lt k.isLt)] at h1
  rw [h]

lemma sum_filter_gt_of_sum_zero (n : ℕ) (a : Fin n → ℝ) (h_sum : ∑ k, a k = 0)
    (j : Fin n) :
    (∑ k ∈ Finset.univ.filter (fun k => j < k), a k) =
      - (∑ k ∈ Finset.univ.filter (fun k => k ≤ j), a k) := by
  have h_split : (∑ k ∈ Finset.univ.filter (fun k => k ≤ j), a k) +
      (∑ k ∈ Finset.univ.filter (fun k => j < k), a k) = ∑ k, a k := by
    rw [← Finset.sum_union]
    · congr 1
      ext x
      simp [le_or_gt]
    · rw [Finset.disjoint_filter]
      intro x _ h1 h2
      omega
  rw [h_sum] at h_split
  linarith

lemma sum_k_mul_eq_neg_sum_partial (n : ℕ) (a : Fin n → ℝ) (h_sum : ∑ k, a k = 0) :
    (∑ k : Fin n, ((k : ℕ) : ℝ) * a k) =
      - ∑ j : Fin n, (∑ k ∈ Finset.univ.filter (fun k => k ≤ j), a k) := by
  have h_lhs : (∑ k : Fin n, ((k : ℕ) : ℝ) * a k) =
      ∑ k : Fin n, ∑ j ∈ Finset.univ.filter (· < k), a k := by
    apply Finset.sum_congr rfl
    intro k _
    rw [sum_filter_lt_const]
  rw [h_lhs, double_sum_triangle]
  have h_rhs : (∑ j : Fin n, ∑ k ∈ Finset.univ.filter (fun k => j < k), a k) =
      ∑ j : Fin n, - (∑ k ∈ Finset.univ.filter (fun k => k ≤ j), a k) := by
    apply Finset.sum_congr rfl
    intro j _
    exact sum_filter_gt_of_sum_zero n a h_sum j
  rw [h_rhs, ← Finset.sum_neg_distrib]

lemma minkowskiInner_add_left (x y z : Fin 4 → ℝ) :
    minkowskiInner (x + y) z = minkowskiInner x z + minkowskiInner y z := by
  simp only [minkowskiInner_explicit, Pi.add_apply]
  ring

lemma minkowskiInner_zero_left (z : Fin 4 → ℝ) :
    minkowskiInner 0 z = 0 := by
  simp only [minkowskiInner_explicit, Pi.zero_apply]
  ring

lemma minkowskiInner_sum_left {ι : Type*} (s : Finset ι) (f : ι → Fin 4 → ℝ) (v : Fin 4 → ℝ) :
    minkowskiInner (∑ i ∈ s, f i) v = ∑ i ∈ s, minkowskiInner (f i) v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [minkowskiInner_zero_left]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, minkowskiInner_add_left, ih]

lemma sum_k_minkowskiInner_le_zero (n : ℕ) (p : Fin n → Fin 4 → ℝ) (hp : p ∈ spectralRegion n)
    (v : Fin 4 → ℝ) (hv : v ∈ forward_light_cone) :
    ∑ k : Fin n, ((k : ℕ) : ℝ) * minkowskiInner (p k) v ≤ 0 := by
  have h_sum0 : (∑ k : Fin n, minkowskiInner (p k) v) = 0 := by
    rw [← minkowskiInner_sum_left, hp.1, minkowskiInner_zero_left]
  rw [sum_k_mul_eq_neg_sum_partial n (fun k => minkowskiInner (p k) v) h_sum0]
  have h_nonneg : 0 ≤ ∑ j : Fin n,
      (∑ k ∈ Finset.univ.filter (fun k => k ≤ j), minkowskiInner (p k) v) := by
    apply Finset.sum_nonneg
    intro j _
    have h_q : (∑ k ∈ Finset.univ.filter (fun k => k ≤ j), minkowskiInner (p k) v) =
        minkowskiInner (partial_sum_p n p j) v := by
      dsimp [partial_sum_p]
      rw [minkowskiInner_sum_left]
    rw [h_q]
    have hq := partial_sum_p_mem_closure n p hp j
    have h_gap := coneGap_pos v hv
    have h_bound := minkowskiInner_ge_coneGap_closure v (partial_sum_p n p j) hq
    have hq_closed := closure_forward_light_cone_subset hq
    have hq0 : 0 ≤ (partial_sum_p n p j) 0 := hq_closed.1
    have h_prod : 0 ≤ coneGap v * (partial_sum_p n p j) 0 :=
      mul_nonneg (le_of_lt h_gap) hq0
    exact h_prod.trans h_bound
  linarith

lemma vladimirov_kernel_line_norm_le_one (n : ℕ) (p : Fin n → Fin 4 → ℝ) (hp : p ∈ spectralRegion n)
    (x : Fin n → Fin 4 → ℝ) (v : Fin 4 → ℝ) (hv : v ∈ forward_light_cone) (t : ℝ) (ht : 0 ≤ t) :
    ‖vladimirov_kernel n
        (fun i k => (x i k : ℂ) + Complex.I * ((t * ((i : ℕ) : ℝ) * v k : ℝ) : ℂ)) p‖ ≤ 1 := by
  rw [vladimirov_kernel_line_norm]
  have h_prod : t * ∑ k : Fin n, ((k : ℕ) : ℝ) * minkowskiInner (p k) v ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos ht (sum_k_minkowskiInner_le_zero n p hp v hv)
  have h_exp := Real.exp_le_exp.mpr h_prod
  rw [Real.exp_zero] at h_exp
  exact h_exp

lemma neg_I_mul_innerC_line (p : Fin 4 → ℝ) (x : Fin 4 → ℝ) (v : Fin 4 → ℝ) (c : ℝ) :
    - Complex.I * minkowskiInnerC (fun μ => (p μ : ℂ))
        (fun μ => (x μ : ℂ) + Complex.I * ((c * v μ : ℝ) : ℂ)) =
      ((c * minkowskiInner p v : ℝ) : ℂ) - Complex.I * ((minkowskiInner p x : ℝ) : ℂ) := by
  have h_re : (fun μ => ((x μ : ℂ) + Complex.I * ((c * v μ : ℝ) : ℂ)).re) = x := by
    ext μ; simp
  have h_im : (fun μ => ((x μ : ℂ) + Complex.I * ((c * v μ : ℝ) : ℂ)).im) = c • v := by
    ext μ; exact add_I_mul_im (x μ) (c * v μ)
  rw [minkowskiInnerC_coe_real, h_re, h_im, minkowskiInner_smul_right]
  ring_nf
  rw [Complex.I_sq]
  ring

lemma vladimirov_kernel_line_eq (n : ℕ) (p : Fin n → Fin 4 → ℝ) (x : Fin n → Fin 4 → ℝ)
    (v : Fin 4 → ℝ) (t : ℝ) :
    vladimirov_kernel n
        (fun i k => (x i k : ℂ) + Complex.I * ((t * ((i : ℕ) : ℝ) * v k : ℝ) : ℂ)) p =
      Complex.exp ((t * ∑ k : Fin n, ((k : ℕ) : ℝ) * minkowskiInner (p k) v : ℂ) -
        Complex.I * (∑ k : Fin n, (minkowskiInner (p k) (x k) : ℂ))) := by
  dsimp [vladimirov_kernel]
  have h_mul : - Complex.I * (∑ k : Fin n, minkowskiInnerC (fun μ => (p k μ : ℂ))
      (fun μ => (x k μ : ℂ) + Complex.I * ((t * ((k : ℕ) : ℝ) * v μ : ℝ) : ℂ))) =
      ∑ k : Fin n, - Complex.I * minkowskiInnerC (fun μ => (p k μ : ℂ))
        (fun μ => (x k μ : ℂ) + Complex.I * ((t * ((k : ℕ) : ℝ) * v μ : ℝ) : ℂ)) := by
    rw [Finset.mul_sum]
  rw [h_mul]
  have h_term : (∑ k : Fin n, - Complex.I * minkowskiInnerC (fun μ => (p k μ : ℂ))
      (fun μ => (x k μ : ℂ) + Complex.I * ((t * ((k : ℕ) : ℝ) * v μ : ℝ) : ℂ))) =
      ∑ k : Fin n, (((t * ((k : ℕ) : ℝ) * minkowskiInner (p k) v : ℝ) : ℂ) -
        Complex.I * ((minkowskiInner (p k) (x k) : ℝ) : ℂ)) := by
    apply Finset.sum_congr rfl
    intro k _
    exact neg_I_mul_innerC_line (p k) (x k) v (t * ((k : ℕ) : ℝ))
  rw [h_term, Finset.sum_sub_distrib]
  congr 1
  congr 1
  · push_cast
    simp_rw [mul_assoc]
    exact (Finset.mul_sum (Finset.univ : Finset (Fin n)) _ (t : ℂ)).symm
  · rw [← Finset.mul_sum]

lemma vladimirov_kernel_line_factor (n : ℕ) (p : Fin n → Fin 4 → ℝ) (x : Fin n → Fin 4 → ℝ)
    (v : Fin 4 → ℝ) (t : ℝ) :
    vladimirov_kernel n
        (fun i k => (x i k : ℂ) + Complex.I * ((t * ((i : ℕ) : ℝ) * v k : ℝ) : ℂ)) p =
      Complex.exp (t * ∑ k : Fin n, ((k : ℕ) : ℝ) * minkowskiInner (p k) v : ℂ) *
      Complex.exp (- (Complex.I * (∑ k : Fin n, (minkowskiInner (p k) (x k) : ℂ)))) := by
  rw [vladimirov_kernel_line_eq, sub_eq_add_neg, Complex.exp_add]

lemma tendsto_vladimirov_kernel_boundary (n : ℕ) (p : Fin n → Fin 4 → ℝ) (x : Fin n → Fin 4 → ℝ)
    (v : Fin 4 → ℝ) :
    Tendsto (fun t : ℝ => vladimirov_kernel n
        (fun i k => (x i k : ℂ) + Complex.I * ((t * ((i : ℕ) : ℝ) * v k : ℝ) : ℂ)) p)
      (𝓝[>] 0)
      (𝓝 (Complex.exp (- Complex.I * (∑ k : Fin n, (minkowskiInner (p k) (x k) : ℂ))))) := by
  have h_eq : (fun t : ℝ => vladimirov_kernel n
        (fun i k => (x i k : ℂ) + Complex.I * ((t * ((i : ℕ) : ℝ) * v k : ℝ) : ℂ)) p) =
      (fun t : ℝ => Complex.exp ((t * ∑ k : Fin n, ((k : ℕ) : ℝ) * minkowskiInner (p k) v : ℂ) -
        Complex.I * (∑ k : Fin n, (minkowskiInner (p k) (x k) : ℂ)))) := by
    ext t
    exact vladimirov_kernel_line_eq n p x v t
  rw [h_eq]
  have h_cont : Continuous (fun t : ℝ => Complex.exp
      ((t * ∑ k : Fin n, ((k : ℕ) : ℝ) * minkowskiInner (p k) v : ℂ) -
        Complex.I * (∑ k : Fin n, (minkowskiInner (p k) (x k) : ℂ)))) := by
    apply Continuous.cexp
    apply Continuous.sub
    · exact Complex.continuous_ofReal.mul continuous_const
    · exact continuous_const
  have h_tend := h_cont.tendsto 0
  have h_zero : ((0 : ℝ) * ∑ k : Fin n, ((k : ℕ) : ℝ) * minkowskiInner (p k) v : ℂ) -
      Complex.I * (∑ k : Fin n, (minkowskiInner (p k) (x k) : ℂ)) =
      - Complex.I * (∑ k : Fin n, (minkowskiInner (p k) (x k) : ℂ)) := by
    simp
  rw [h_zero] at h_tend
  exact h_tend.mono_left nhdsWithin_le_nhds

lemma integral_f_mul_vladimirov_kernel_line (n : ℕ) (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    (p : Fin n → Fin 4 → ℝ) (v : Fin 4 → ℝ) (t : ℝ) :
    (∫ x : Fin n → Fin 4 → ℝ, f x * vladimirov_kernel n
        (fun i k => (x i k : ℂ) + Complex.I * ((t * ((i : ℕ) : ℝ) * v k : ℝ) : ℂ)) p) =
      Complex.exp (t * ∑ k : Fin n, ((k : ℕ) : ℝ) * minkowskiInner (p k) v : ℂ) *
        minkowskiFourier f p := by
  dsimp [minkowskiFourier]
  have h_sum_cast : ∀ (x : Fin n → Fin 4 → ℝ),
      (∑ k : Fin n, (minkowskiInner (p k) (x k) : ℂ)) =
      ((∑ k : Fin n, minkowskiInner (p k) (x k) : ℝ) : ℂ) := by
    intro x
    push_cast
    rfl
  have h_eq : (fun x => f x * vladimirov_kernel n
        (fun i k => (x i k : ℂ) + Complex.I * ((t * ((i : ℕ) : ℝ) * v k : ℝ) : ℂ)) p) =
      (fun x => Complex.exp (t * ∑ k : Fin n, ((k : ℕ) : ℝ) * minkowskiInner (p k) v : ℂ) *
        (f x * Complex.exp (- (Complex.I * ((∑ k, minkowskiInner (p k) (x k) : ℝ) : ℂ))))) := by
    ext x
    rw [vladimirov_kernel_line_factor, h_sum_cast x]
    ring
  rw [h_eq, integral_const_mul]

lemma tendsto_integral_f_mul_vladimirov_kernel_line (n : ℕ) (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    (p : Fin n → Fin 4 → ℝ) (v : Fin 4 → ℝ) :
    Tendsto (fun t : ℝ => ∫ x : Fin n → Fin 4 → ℝ, f x * vladimirov_kernel n
        (fun i k => (x i k : ℂ) + Complex.I * ((t * ((i : ℕ) : ℝ) * v k : ℝ) : ℂ)) p)
      (𝓝[>] 0)
      (𝓝 (minkowskiFourier f p)) := by
  have h_eq : (fun t : ℝ => ∫ x : Fin n → Fin 4 → ℝ, f x * vladimirov_kernel n
        (fun i k => (x i k : ℂ) + Complex.I * ((t * ((i : ℕ) : ℝ) * v k : ℝ) : ℂ)) p) =
      (fun t : ℝ => Complex.exp (t * ∑ k : Fin n, ((k : ℕ) : ℝ) * minkowskiInner (p k) v : ℂ) *
        minkowskiFourier f p) := by
    ext t
    exact integral_f_mul_vladimirov_kernel_line n f p v t
  rw [h_eq]
  have h_cont : Continuous (fun t : ℝ => Complex.exp
      (t * ∑ k : Fin n, ((k : ℕ) : ℝ) * minkowskiInner (p k) v : ℂ) * minkowskiFourier f p) := by
    apply Continuous.mul
    · apply Continuous.cexp
      exact Complex.continuous_ofReal.mul continuous_const
    · exact continuous_const
  have h_tend := h_cont.tendsto 0
  have h_zero : Complex.exp ((0 : ℝ) * ∑ k : Fin n, ((k : ℕ) : ℝ) * minkowskiInner (p k) v : ℂ) *
      minkowskiFourier f p = minkowskiFourier f p := by
    simp
  rw [h_zero] at h_tend
  exact h_tend.mono_left nhdsWithin_le_nhds

noncomputable def vladimirov_phase_LM (n : ℕ) (z : Fin n → Fin 4 → ℂ) :
    (Fin n → Fin 4 → ℝ) →ₗ[ℝ] ℂ where
  toFun p := - Complex.I * (∑ k : Fin n, minkowskiInnerC (fun μ => (p k μ : ℂ)) (z k))
  map_add' p q := by
    simp only [Pi.add_apply]
    have h_inner : ∀ k : Fin n,
        minkowskiInnerC (fun μ => ((p k μ + q k μ : ℝ) : ℂ)) (z k) =
        minkowskiInnerC (fun μ => (p k μ : ℂ)) (z k) +
        minkowskiInnerC (fun μ => (q k μ : ℂ)) (z k) := by
      intro k
      dsimp [minkowskiInnerC]
      push_cast
      ring
    simp_rw [h_inner, Finset.sum_add_distrib]
    ring
  map_smul' c p := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    have h_inner : ∀ k : Fin n,
        minkowskiInnerC (fun μ => ((c * p k μ : ℝ) : ℂ)) (z k) =
        (c : ℂ) * minkowskiInnerC (fun μ => (p k μ : ℂ)) (z k) := by
      intro k
      dsimp [minkowskiInnerC]
      push_cast
      ring
    simp_rw [h_inner, ← Finset.mul_sum]
    dsimp [HSMul.hSMul, SMul.smul]
    ring

noncomputable def vladimirov_phase_CLM (n : ℕ) (z : Fin n → Fin 4 → ℂ) :
    (Fin n → Fin 4 → ℝ) →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap (vladimirov_phase_LM n z)

noncomputable def vladimirov_phase_z_LM (n : ℕ) (p : Fin n → Fin 4 → ℝ) :
    (Fin n → Fin 4 → ℂ) →ₗ[ℂ] ℂ where
  toFun z := - Complex.I * (∑ k : Fin n, minkowskiInnerC (fun μ => (p k μ : ℂ)) (z k))
  map_add' z w := by
    simp only [Pi.add_apply]
    have h_inner : ∀ k : Fin n,
        minkowskiInnerC (fun μ => (p k μ : ℂ)) (z k + w k) =
        minkowskiInnerC (fun μ => (p k μ : ℂ)) (z k) +
        minkowskiInnerC (fun μ => (p k μ : ℂ)) (w k) := by
      intro k
      dsimp [minkowskiInnerC]
      ring
    simp_rw [h_inner, Finset.sum_add_distrib]
    ring
  map_smul' c z := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    have h_inner : ∀ k : Fin n,
        minkowskiInnerC (fun μ => (p k μ : ℂ)) (c • z k) =
        c * minkowskiInnerC (fun μ => (p k μ : ℂ)) (z k) := by
      intro k
      dsimp [minkowskiInnerC]
      ring
    simp_rw [h_inner, ← Finset.mul_sum]
    ring

noncomputable def vladimirov_phase_z_CLM (n : ℕ) (p : Fin n → Fin 4 → ℝ) :
    (Fin n → Fin 4 → ℂ) →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap (vladimirov_phase_z_LM n p)

lemma vladimirov_phase_z_CLM_add (n : ℕ) (p : Fin n → Fin 4 → ℝ) (h1 h2 : Fin n → Fin 4 → ℂ) :
    (vladimirov_phase_z_CLM n p) (h1 + h2) =
    (vladimirov_phase_z_CLM n p) h1 + (vladimirov_phase_z_CLM n p) h2 :=
  map_add (vladimirov_phase_z_CLM n p) h1 h2

lemma vladimirov_phase_z_CLM_smul (n : ℕ) (p : Fin n → Fin 4 → ℝ) (c : ℂ) (h : Fin n → Fin 4 → ℂ) :
    (vladimirov_phase_z_CLM n p) (c • h) =
    c • (vladimirov_phase_z_CLM n p) h :=
  map_smul (vladimirov_phase_z_CLM n p) c h

lemma vladimirov_kernel_analyticAt (n : ℕ) (p : Fin n → Fin 4 → ℝ) (z : Fin n → Fin 4 → ℂ) :
    AnalyticAt ℂ (fun w : Fin n → Fin 4 → ℂ => vladimirov_kernel n w p) z := by
  have h_eq : (fun w => vladimirov_kernel n w p) =
      Complex.exp ∘ (vladimirov_phase_z_CLM n p) := by
    ext w
    rfl
  rw [h_eq]
  exact AnalyticAt.cexp ((vladimirov_phase_z_CLM n p).analyticAt z)

lemma vladimirov_kernel_contDiff (n : ℕ) (z : Fin n → Fin 4 → ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : Fin n → Fin 4 → ℝ => vladimirov_kernel n z p) := by
  have h_eq : (fun p => vladimirov_kernel n z p) =
      Complex.exp ∘ (vladimirov_phase_CLM n z) := by
    ext p
    rfl
  rw [h_eq]
  exact Complex.contDiff_exp.comp (vladimirov_phase_CLM n z).contDiff

def vladimirovCutoffBump (n : ℕ) (R : ℝ) (hR : 0 < R) :
    ContDiffBump (0 : Fin n → Fin 4 → ℝ) where
  rIn := R
  rOut := 2 * R
  rIn_pos := hR
  rIn_lt_rOut := by linarith

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirovCutoffBump_nonneg_and_le_one (n : ℕ) (q : Fin n → Fin 4 → ℝ) :
    0 ≤ vladimirovCutoffBump n 1 Real.zero_lt_one q ∧
    vladimirovCutoffBump n 1 Real.zero_lt_one q ≤ 1 :=
  ⟨(vladimirovCutoffBump n 1 Real.zero_lt_one).nonneg,
   (vladimirovCutoffBump n 1 Real.zero_lt_one).le_one⟩

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirovCutoffBump_eq_zero_of_two_le (n : ℕ) (q : Fin n → Fin 4 → ℝ)
    (hq : 2 ≤ ‖q‖) :
    vladimirovCutoffBump n 1 Real.zero_lt_one q = 0 := by
  have h_dist : (vladimirovCutoffBump n 1 Real.zero_lt_one).rOut ≤ dist q 0 := by
    dsimp [vladimirovCutoffBump]
    rw [dist_zero_right]
    linarith
  exact (vladimirovCutoffBump n 1 Real.zero_lt_one).zero_of_le_dist h_dist

noncomputable def vladimirov_psi (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z : Fin n → Fin 4 → ℂ) (p : Fin n → Fin 4 → ℝ) : ℂ :=
  ((vladimirovCutoffBump n R hR p : ℝ) : ℂ) * vladimirov_kernel n z p

lemma vladimirov_psi_analyticAt (n : ℕ) (R : ℝ) (hR : 0 < R)
    (p : Fin n → Fin 4 → ℝ) (z : Fin n → Fin 4 → ℂ) :
    AnalyticAt ℂ (fun w : Fin n → Fin 4 → ℂ => vladimirov_psi n R hR w p) z := by
  dsimp [vladimirov_psi]
  exact analyticAt_const.mul (vladimirov_kernel_analyticAt n p z)

lemma vladimirov_kernel_differentiableAt (n : ℕ) (p : Fin n → Fin 4 → ℝ)
    (z : Fin n → Fin 4 → ℂ) :
    DifferentiableAt ℂ (fun w => vladimirov_kernel n w p) z :=
  (vladimirov_kernel_analyticAt n p z).differentiableAt

lemma vladimirov_psi_differentiableAt (n : ℕ) (R : ℝ) (hR : 0 < R)
    (p : Fin n → Fin 4 → ℝ) (z : Fin n → Fin 4 → ℂ) :
    DifferentiableAt ℂ (fun w => vladimirov_psi n R hR w p) z :=
  (vladimirov_psi_analyticAt n R hR p z).differentiableAt

lemma vladimirov_psi_hasCompactSupport (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z : Fin n → Fin 4 → ℂ) :
    HasCompactSupport (vladimirov_psi n R hR z) := by
  have h_supp : HasCompactSupport (fun p => ((vladimirovCutoffBump n R hR p : ℝ) : ℂ)) := by
    have h1 := (vladimirovCutoffBump n R hR).hasCompactSupport
    exact h1.comp_left (g := fun (r : ℝ) => (r : ℂ)) Complex.ofReal_zero
  change HasCompactSupport
    (fun p => ((vladimirovCutoffBump n R hR p : ℝ) : ℂ) * vladimirov_kernel n z p)
  exact h_supp.mul_right

lemma vladimirov_psi_contDiff (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z : Fin n → Fin 4 → ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (vladimirov_psi n R hR z) := by
  have h_bump : ContDiff ℝ (⊤ : ℕ∞) (fun p => ((vladimirovCutoffBump n R hR p : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (vladimirovCutoffBump n R hR).contDiff
  change ContDiff ℝ (⊤ : ℕ∞)
    (fun p => ((vladimirovCutoffBump n R hR p : ℝ) : ℂ) * vladimirov_kernel n z p)
  exact h_bump.mul (vladimirov_kernel_contDiff n z)

noncomputable def vladimirov_psi_schwartz (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z : Fin n → Fin 4 → ℂ) :
    SchwartzMap (Fin n → Fin 4 → ℝ) ℂ :=
  (vladimirov_psi_hasCompactSupport n R hR z).toSchwartzMap
    (vladimirov_psi_contDiff n R hR z)

lemma vladimirov_deriv_psi_contDiff (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z h : Fin n → Fin 4 → ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p => (vladimirov_phase_CLM n h p) * vladimirov_psi n R hR z p) := by
  apply ContDiff.mul
  · exact (vladimirov_phase_CLM n h).contDiff
  · exact vladimirov_psi_contDiff n R hR z

lemma vladimirov_deriv_psi_hasCompactSupport (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z h : Fin n → Fin 4 → ℂ) :
    HasCompactSupport (fun p => (vladimirov_phase_CLM n h p) * vladimirov_psi n R hR z p) := by
  have h_supp : HasCompactSupport (vladimirov_psi n R hR z) :=
    vladimirov_psi_hasCompactSupport n R hR z
  exact h_supp.mul_left

noncomputable def vladimirov_deriv_psi_schwartz (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z h : Fin n → Fin 4 → ℂ) :
    SchwartzMap (Fin n → Fin 4 → ℝ) ℂ :=
  (vladimirov_deriv_psi_hasCompactSupport n R hR z h).toSchwartzMap
    (vladimirov_deriv_psi_contDiff n R hR z h)

lemma vladimirov_phase_clm_eq_phase_z_clm (n : ℕ) (h : Fin n → Fin 4 → ℂ) (p : Fin n → Fin 4 → ℝ) :
    (vladimirov_phase_CLM n h) p = (vladimirov_phase_z_CLM n p) h := by
  dsimp [vladimirov_phase_CLM, vladimirov_phase_z_CLM, vladimirov_phase_LM, vladimirov_phase_z_LM]

lemma vladimirov_deriv_psi_add_eval (n : ℕ) (R : ℝ) (hR : 0 < R) (z : Fin n → Fin 4 → ℂ)
    (h1 h2 : Fin n → Fin 4 → ℂ) (p : Fin n → Fin 4 → ℝ) :
    ((vladimirov_phase_CLM n (h1 + h2) p) * vladimirov_psi n R hR z p) =
    (vladimirov_phase_CLM n h1 p) * vladimirov_psi n R hR z p +
    (vladimirov_phase_CLM n h2 p) * vladimirov_psi n R hR z p := by
  rw [vladimirov_phase_clm_eq_phase_z_clm n (h1 + h2),
      vladimirov_phase_clm_eq_phase_z_clm n h1,
      vladimirov_phase_clm_eq_phase_z_clm n h2]
  rw [vladimirov_phase_z_CLM_add]
  ring

lemma vladimirov_deriv_psi_smul_eval (n : ℕ) (R : ℝ) (hR : 0 < R) (z : Fin n → Fin 4 → ℂ)
    (c : ℂ) (h : Fin n → Fin 4 → ℂ) (p : Fin n → Fin 4 → ℝ) :
    ((vladimirov_phase_CLM n (c • h) p) * vladimirov_psi n R hR z p) =
    c * ((vladimirov_phase_CLM n h p) * vladimirov_psi n R hR z p) := by
  rw [vladimirov_phase_clm_eq_phase_z_clm n (c • h),
      vladimirov_phase_clm_eq_phase_z_clm n h]
  rw [vladimirov_phase_z_CLM_smul]
  dsimp [HSMul.hSMul, SMul.smul]
  ring

lemma integral_f_mul_vladimirov_psi (n : ℕ) (R : ℝ) (hR : 0 < R)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    (p : Fin n → Fin 4 → ℝ) (v : Fin 4 → ℝ) (t : ℝ) :
    (∫ x : Fin n → Fin 4 → ℝ, f x * vladimirov_psi n R hR
        (fun i k => (x i k : ℂ) + Complex.I * ((t * ((i : ℕ) : ℝ) * v k : ℝ) : ℂ)) p) =
      ((vladimirovCutoffBump n R hR p : ℝ) : ℂ) *
        (Complex.exp (t * ∑ k : Fin n, ((k : ℕ) : ℝ) * minkowskiInner (p k) v : ℂ) *
          minkowskiFourier f p) := by
  dsimp [vladimirov_psi]
  have h_eq : (fun x => f x * (((vladimirovCutoffBump n R hR p : ℝ) : ℂ) *
        vladimirov_kernel n (fun i k =>
          (x i k : ℂ) + Complex.I * ((t * ((i : ℕ) : ℝ) * v k : ℝ) : ℂ)) p)) =
      (fun x => ((vladimirovCutoffBump n R hR p : ℝ) : ℂ) *
        (f x * vladimirov_kernel n (fun i k =>
          (x i k : ℂ) + Complex.I * ((t * ((i : ℕ) : ℝ) * v k : ℝ) : ℂ)) p)) := by
    ext x
    ring
  rw [h_eq, integral_const_mul, integral_f_mul_vladimirov_kernel_line]

lemma tendsto_integral_f_mul_vladimirov_psi (n : ℕ) (R : ℝ) (hR : 0 < R)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    (p : Fin n → Fin 4 → ℝ) (v : Fin 4 → ℝ) :
    Tendsto (fun t : ℝ => ∫ x : Fin n → Fin 4 → ℝ, f x * vladimirov_psi n R hR
        (fun i k => (x i k : ℂ) + Complex.I * ((t * ((i : ℕ) : ℝ) * v k : ℝ) : ℂ)) p)
      (𝓝[>] 0)
      (𝓝 (((vladimirovCutoffBump n R hR p : ℝ) : ℂ) * minkowskiFourier f p)) := by
  have h_eq : (fun t : ℝ => ∫ x : Fin n → Fin 4 → ℝ, f x * vladimirov_psi n R hR
        (fun i k => (x i k : ℂ) + Complex.I * ((t * ((i : ℕ) : ℝ) * v k : ℝ) : ℂ)) p) =
      (fun t : ℝ => ((vladimirovCutoffBump n R hR p : ℝ) : ℂ) *
        (Complex.exp (t * ∑ k : Fin n, ((k : ℕ) : ℝ) * minkowskiInner (p k) v : ℂ) *
          minkowskiFourier f p)) := by
    ext t
    exact integral_f_mul_vladimirov_psi n R hR f p v t
  rw [h_eq]
  have h_conv := tendsto_integral_f_mul_vladimirov_kernel_line n f p v
  have h_eq2 : (fun t : ℝ => ((vladimirovCutoffBump n R hR p : ℝ) : ℂ) *
        (Complex.exp (t * ∑ k : Fin n, ((k : ℕ) : ℝ) * minkowskiInner (p k) v : ℂ) *
          minkowskiFourier f p)) =
      (fun t : ℝ => ((vladimirovCutoffBump n R hR p : ℝ) : ℂ) *
        (∫ x : Fin n → Fin 4 → ℝ, f x * vladimirov_kernel n
          (fun i k => (x i k : ℂ) + Complex.I * ((t * ((i : ℕ) : ℝ) * v k : ℝ) : ℂ)) p)) := by
    ext t
    rw [integral_f_mul_vladimirov_kernel_line]
  rw [h_eq2]
  exact h_conv.const_mul ((vladimirovCutoffBump n R hR p : ℝ) : ℂ)

def minkowskiFlipFun (n : ℕ) (x : Fin n → Fin 4 → ℝ) : Fin n → Fin 4 → ℝ :=
  fun i k => if k = 0 then x i 0 else - x i k

lemma minkowskiFlipFun_involutive (n : ℕ) (x : Fin n → Fin 4 → ℝ) :
    minkowskiFlipFun n (minkowskiFlipFun n x) = x := by
  ext i k
  dsimp [minkowskiFlipFun]
  split_ifs with hk
  · subst hk; rfl
  · simp

noncomputable def minkowskiFlipEquiv (n : ℕ) :
    (Fin n → Fin 4 → ℝ) ≃L[ℝ] (Fin n → Fin 4 → ℝ) :=
  LinearEquiv.toContinuousLinearEquiv {
    toFun := minkowskiFlipFun n
    invFun := minkowskiFlipFun n
    left_inv := minkowskiFlipFun_involutive n
    right_inv := minkowskiFlipFun_involutive n
    map_add' := fun x y => by
      ext i k
      dsimp [minkowskiFlipFun]
      split_ifs <;> ring
    map_smul' := fun c x => by
      ext i k
      dsimp [minkowskiFlipFun]
      split_ifs <;> ring
  }

noncomputable def finCurryEquiv (n : ℕ) : (Fin n → Fin 4 → ℝ) ≃L[ℝ] ((Fin n × Fin 4) → ℝ) :=
  LinearEquiv.toContinuousLinearEquiv {
    toFun := fun f (i, k) => f i k
    invFun := fun g i k => g (i, k)
    left_inv := fun _ => rfl
    right_inv := fun _ => funext fun ⟨_, _⟩ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl
  }

noncomputable def finEuclidEquiv (n : ℕ) :
    ((Fin n × Fin 4) → ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin n × Fin 4) :=
  (EuclideanSpace.equiv (Fin n × Fin 4) ℝ).symm

noncomputable def piSpaceEquiv (n : ℕ) :
    (Fin n → Fin 4 → ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin n × Fin 4) :=
  (finCurryEquiv n).trans (finEuclidEquiv n)

noncomputable def invMinkowskiFourierCLM (n : ℕ) :
    SchwartzMap (Fin n → Fin 4 → ℝ) ℂ →L[ℂ] SchwartzMap (Fin n → Fin 4 → ℝ) ℂ :=
  (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (minkowskiFlipEquiv n)).comp
    ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (piSpaceEquiv n)).comp
      ((SchwartzMap.fourierTransformCLM ℂ).comp
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (piSpaceEquiv n).symm)))

noncomputable def vladimirov_H_cutoff (W : WightmanFamily ι) (n : ℕ) (R : ℝ) (hR : 0 < R)
    (α : Fin n → ι) (z : Fin n → Fin 4 → ℂ) : ℂ :=
  W n α (invMinkowskiFourierCLM n (vladimirov_psi_schwartz n R hR z))

noncomputable def vladimirov_H (W : WightmanFamily ι) (n : ℕ) (α : Fin n → ι)
    (z : Fin n → Fin 4 → ℂ) : ℂ :=
  vladimirov_H_cutoff W n 1 Real.zero_lt_one α z

lemma forward_tube_n_isOpen (n : ℕ) : IsOpen (forward_tube_n n) := by
  dsimp [forward_tube_n]
  simp_rw [Set.setOf_forall]
  apply isOpen_iInter_of_finite
  intro i
  apply isOpen_iInter_of_finite
  intro hi
  apply IsOpen.preimage
  · apply continuous_pi
    intro k
    apply Continuous.neg
    apply Continuous.sub
    · exact Complex.continuous_im.comp ((continuous_apply k).comp (continuous_apply i))
    · exact Complex.continuous_im.comp
        ((continuous_apply k).comp (continuous_apply (⟨i.val + 1, hi⟩ : Fin n)))
  · exact forward_light_cone_isOpen

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_H_analyticOn_iff (W : WightmanFamily ι) (n : ℕ) (α : Fin n → ι) :
    AnalyticOn ℂ (vladimirov_H W n α) (forward_tube_n n) ↔
    ∀ z ∈ forward_tube_n n, AnalyticAt ℂ (vladimirov_H W n α) z := by
  rw [(forward_tube_n_isOpen n).analyticOn_iff_analyticOnNhd]
  rfl

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_H_analytic_zero (W : WightmanFamily ι) (α : Fin 0 → ι) :
    AnalyticOn ℂ (vladimirov_H W 0 α) (forward_tube_n 0) := by
  have h_const : ∀ z w : Fin 0 → Fin 4 → ℂ, vladimirov_H W 0 α z = vladimirov_H W 0 α w := by
    intro z w
    have h_eq : z = w := Subsingleton.elim z w
    rw [h_eq]
  let z0 : Fin 0 → Fin 4 → ℂ := fun i => Fin.elim0 i
  have h_fun_eq : (vladimirov_H W 0 α) = fun _ => vladimirov_H W 0 α z0 := by
    ext z
    exact h_const z z0
  rw [h_fun_eq]
  exact analyticOn_const

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_H_analytic_at_zero (W : WightmanFamily ι) (α : Fin 0 → ι)
    (z : Fin 0 → Fin 4 → ℂ) :
    AnalyticAt ℂ (vladimirov_H W 0 α) z := by
  have h_const : ∀ z w : Fin 0 → Fin 4 → ℂ, vladimirov_H W 0 α z = vladimirov_H W 0 α w := by
    intro z w
    have h_eq : z = w := Subsingleton.elim z w
    rw [h_eq]
  let z0 : Fin 0 → Fin 4 → ℂ := fun i => Fin.elim0 i
  have h_fun_eq : (vladimirov_H W 0 α) = fun _ => vladimirov_H W 0 α z0 := by
    ext w
    exact h_const w z0
  rw [h_fun_eq]
  exact analyticAt_const

def SchwartzFamilyAnalyticAt (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z : Fin n → Fin 4 → ℂ) : Prop :=
  ∀ (T : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ →L[ℂ] ℂ),
    AnalyticAt ℂ (fun w => T (vladimirov_psi_schwartz n R hR w)) z

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_H_analyticAt_of_family (W : WightmanFamily ι) (n : ℕ) (α : Fin n → ι)
    (z : Fin n → Fin 4 → ℂ) (h_fam : SchwartzFamilyAnalyticAt n 1 Real.zero_lt_one z) :
    AnalyticAt ℂ (vladimirov_H W n α) z := by
  let T : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ →L[ℂ] ℂ :=
    (W n α).comp (invMinkowskiFourierCLM n)
  exact h_fam T

lemma shift_zero_of_fin_one (t : ℝ) (v : Fin 4 → ℝ) (x : Fin 1 → Fin 4 → ℝ) :
    (fun (i : Fin 1) (k : Fin 4) => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ)) =
    (fun i k => (x i k : ℂ)) := by
  ext i k
  have hi : (i : ℕ) = 0 := by
    fin_cases i
    rfl
  rw [hi]
  ring_nf
  simp

lemma shift_zero_of_fin_zero (t : ℝ) (v : Fin 4 → ℝ) (x : Fin 0 → Fin 4 → ℝ) :
    (fun (i : Fin 0) (k : Fin 4) => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ)) =
    (fun i k => (x i k : ℂ)) := by
  ext i
  exact Fin.elim0 i

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_cutoff_lorentz_diff_one (W : WightmanFamily ι)
    (n : ℕ) (z : Fin n → Fin 4 → ℂ) (α : Fin n → ι) :
    W n α (invMinkowskiFourierCLM n
      (vladimirov_psi_schwartz n 1 Real.zero_lt_one
        (spinorPhi ((1 : SL2C), sl2c_conj (1 : SL2C)) • z))) =
    W n α (schwartzLorentzCLM n (1 : SL2C)⁻¹
      (invMinkowskiFourierCLM n (vladimirov_psi_schwartz n 1 Real.zero_lt_one z))) := by
  have h_conj : sl2c_conj (1 : SL2C) = 1 := sl2c_conj_one
  rw [h_conj]
  have h_phi : spinorPhi ((1 : SL2C), (1 : SL2C)) = 1 := map_one spinorPhi
  rw [h_phi]
  have h_smul : ((1 : SpecialSpecialComplexLorentzGroup) • z) = z := one_smul _ z
  rw [h_smul, inv_one]
  have h_clm : schwartzLorentzCLM n 1 = ContinuousLinearMap.id ℂ _ := by
    ext f x
    rw [schwartzLorentzCLM_apply]
    simp only [lorentzOfSL2C_one, Matrix.one_mulVec, ContinuousLinearMap.id_apply]
  rw [h_clm, ContinuousLinearMap.id_apply]

lemma minkowskiFourier_zero (n : ℕ) (p : Fin n → Fin 4 → ℝ) :
    minkowskiFourier (0 : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) p = 0 := by
  simp [minkowskiFourier]

lemma minkowskiFourier_cutoff_lorentz_diff_one (n : ℕ) (z : Fin n → Fin 4 → ℂ) :
    ∃ U : Set (Fin n → Fin 4 → ℝ), IsOpen U ∧ spectralRegion n ⊆ U ∧
      ∀ p ∈ U, minkowskiFourier
        (invMinkowskiFourierCLM n
          (vladimirov_psi_schwartz n 1 Real.zero_lt_one
            (spinorPhi ((1 : SL2C), sl2c_conj (1 : SL2C)) • z)) -
         schwartzLorentzCLM n (1 : SL2C)⁻¹
          (invMinkowskiFourierCLM n (vladimirov_psi_schwartz n 1 Real.zero_lt_one z))) p = 0 := by
  have h_conj : sl2c_conj (1 : SL2C) = 1 := sl2c_conj_one
  rw [h_conj]
  have h_phi : spinorPhi ((1 : SL2C), (1 : SL2C)) = 1 := map_one spinorPhi
  rw [h_phi]
  have h_smul : ((1 : SpecialSpecialComplexLorentzGroup) • z) = z := one_smul _ z
  rw [h_smul, inv_one]
  have h_clm : schwartzLorentzCLM n 1 = ContinuousLinearMap.id ℂ _ := by
    ext f x
    rw [schwartzLorentzCLM_apply]
    simp only [lorentzOfSL2C_one, Matrix.one_mulVec, ContinuousLinearMap.id_apply]
  rw [h_clm, ContinuousLinearMap.id_apply, sub_self]
  refine ⟨Set.univ, isOpen_univ, Set.subset_univ _, fun p _ => minkowskiFourier_zero n p⟩

lemma lorentzActLM_zero (A : SL2C) (x : Fin 0 → Fin 4 → ℝ) :
    lorentzActLM 0 A x = x := by
  ext i
  exact Fin.elim0 i

lemma spinorPhi_smul_zero (A : SL2C) (z : Fin 0 → Fin 4 → ℂ) :
    (spinorPhi (A, sl2c_conj A) • z) = z := by
  ext i
  exact Fin.elim0 i

lemma schwartzLorentzCLM_zero (A : SL2C) :
    schwartzLorentzCLM 0 A = ContinuousLinearMap.id ℂ _ := by
  ext f x
  rw [schwartzLorentzCLM_apply]
  congr 1
  ext i
  exact Fin.elim0 i

lemma minkowskiFourier_cutoff_lorentz_diff_n0 (A : SL2C) (z : Fin 0 → Fin 4 → ℂ) :
    ∃ U : Set (Fin 0 → Fin 4 → ℝ), IsOpen U ∧ spectralRegion 0 ⊆ U ∧
      ∀ p ∈ U, minkowskiFourier
        (invMinkowskiFourierCLM 0
          (vladimirov_psi_schwartz 0 1 Real.zero_lt_one (spinorPhi (A, sl2c_conj A) • z)) -
         schwartzLorentzCLM 0 A⁻¹
          (invMinkowskiFourierCLM 0 (vladimirov_psi_schwartz 0 1 Real.zero_lt_one z))) p = 0 := by
  rw [spinorPhi_smul_zero, schwartzLorentzCLM_zero, ContinuousLinearMap.id_apply, sub_self]
  refine ⟨Set.univ, isOpen_univ, Set.subset_univ _, fun p _ => minkowskiFourier_zero 0 p⟩

lemma spectralRegion_one (p : Fin 1 → Fin 4 → ℝ) (hp : p ∈ spectralRegion 1) :
    p 0 = 0 := by
  have h_sum := hp.1
  simp only [Fin.sum_univ_one] at h_sum
  exact h_sum

lemma spectralRegion_one_eq_zero (p : Fin 1 → Fin 4 → ℝ) (hp : p ∈ spectralRegion 1) :
    p = 0 := by
  ext i μ
  have hi : i = 0 := Subsingleton.elim i 0
  subst hi
  have h0 := spectralRegion_one p hp
  exact congr_fun h0 μ

lemma spinorPhi_inv_smul (n : ℕ) (A : SL2C) (z : Fin n → Fin 4 → ℂ) :
    spinorPhi (A⁻¹, sl2c_conj A⁻¹) • (spinorPhi (A, sl2c_conj A) • z) = z := by
  have h := (mul_smul (spinorPhi (A⁻¹, sl2c_conj A⁻¹)) (spinorPhi (A, sl2c_conj A)) z).symm
  apply Eq.trans h
  have h_prod : (spinorPhi (A⁻¹, sl2c_conj A⁻¹) * spinorPhi (A, sl2c_conj A)) = 1 := by
    rw [← map_mul]
    have h_pair : ((A⁻¹, sl2c_conj A⁻¹) * (A, sl2c_conj A)) = 1 := by
      ext <;> simp [sl2c_conj_inv]
    rw [h_pair, map_one]
  rw [h_prod]
  exact one_smul _ z

lemma vladimirov_kernel_lorentz_inv (n : ℕ) (A : SL2C)
    (z : Fin n → Fin 4 → ℂ) (p : Fin n → Fin 4 → ℝ) :
    vladimirov_kernel n (spinorPhi (A, sl2c_conj A) • z) p =
    vladimirov_kernel n z (fun k => (lorentzOfSL2C A⁻¹).mulVec (p k)) := by
  have h := (vladimirov_kernel_lorentz n A⁻¹ (spinorPhi (A, sl2c_conj A) • z) p).symm
  rw [h, spinorPhi_inv_smul]

lemma vladimirov_kernel_lorentz_diff (n : ℕ) (A : SL2C)
    (z : Fin n → Fin 4 → ℂ) (p : Fin n → Fin 4 → ℝ) :
    vladimirov_kernel n (spinorPhi (A, sl2c_conj A) • z) ((lorentzEquiv n A) p) =
    vladimirov_kernel n z p := by
  dsimp [lorentzEquiv, lorentzActLM]
  exact vladimirov_kernel_lorentz n A z p

lemma vladimirov_kernel_lorentz_diff_inv (n : ℕ) (A : SL2C)
    (z : Fin n → Fin 4 → ℂ) (p : Fin n → Fin 4 → ℝ) :
    vladimirov_kernel n (spinorPhi (A, sl2c_conj A) • z) p =
    vladimirov_kernel n z ((lorentzEquiv n A⁻¹) p) := by
  have h := vladimirov_kernel_lorentz_inv n A z p
  dsimp [lorentzEquiv, lorentzActLM]
  exact h

noncomputable def vladimirov_psi_com (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z : Fin n → Fin 4 → ℂ) (p : Fin n → Fin 4 → ℝ) : ℂ :=
  ((comCutoff n R hR p : ℝ) : ℂ) * vladimirov_kernel n z p

lemma vladimirov_psi_com_lorentz_diff_zero (n : ℕ) (A : SL2C) (R : ℝ) (hR : 0 < R)
    (z : Fin n → Fin 4 → ℂ) (p : Fin n → Fin 4 → ℝ)
    (hp : p ∈ comNeighborhood n A R) :
    vladimirov_psi_com n R hR (spinorPhi (A, sl2c_conj A) • z) p -
      vladimirov_psi_com n R hR z ((lorentzEquiv n A⁻¹) p) = 0 := by
  dsimp [vladimirov_psi_com]
  have ⟨h1, h2⟩ := comCutoff_lorentz_eq_one n A R hR p hp
  have h_inv := vladimirov_kernel_lorentz_diff_inv n A z p
  rw [h1, h2, h_inv]
  push_cast
  ring

theorem vladimirov_psi_com_diff_vanishes_on_spectralRegion
    (n : ℕ) (A : SL2C) (R : ℝ) (hR : 0 < R) (z : Fin n → Fin 4 → ℂ) :
    ∃ U : Set (Fin n → Fin 4 → ℝ), IsOpen U ∧ spectralRegion n ⊆ U ∧
      ∀ p ∈ U, vladimirov_psi_com n R hR (spinorPhi (A, sl2c_conj A) • z) p -
               vladimirov_psi_com n R hR z ((lorentzEquiv n A⁻¹) p) = 0 := by
  refine ⟨comNeighborhood n A R, isOpen_comNeighborhood n A R,
          spectralRegion_subset_comNeighborhood n A R hR, ?_⟩
  intro p hp
  exact vladimirov_psi_com_lorentz_diff_zero n A R hR z p hp

lemma vladimirov_cutoff_bump_one_of_mem_ball_gen (n : ℕ) (r : ℝ) (hr : r ≤ 1)
    (p : Fin n → Fin 4 → ℝ) (hp : p ∈ Metric.ball (0 : Fin n → Fin 4 → ℝ) r) :
    (vladimirovCutoffBump n 1 Real.zero_lt_one p : ℝ) = 1 := by
  apply (vladimirovCutoffBump n 1 Real.zero_lt_one).one_of_mem_closedBall
  rw [Metric.mem_closedBall, dist_zero_right]
  rw [Metric.mem_ball, dist_zero_right] at hp
  exact hp.le.trans hr

def cutoffNeighborhood (n : ℕ) (A : SL2C) : Set (Fin n → Fin 4 → ℝ) :=
  Metric.ball (0 : Fin n → Fin 4 → ℝ) 1 ∩ (lorentzEquiv n A⁻¹) ⁻¹' (Metric.ball 0 1)

lemma isOpen_cutoffNeighborhood (n : ℕ) (A : SL2C) :
    IsOpen (cutoffNeighborhood n A) := by
  apply IsOpen.inter Metric.isOpen_ball
  exact Metric.isOpen_ball.preimage (lorentzEquiv n A⁻¹).continuous

lemma cutoff_eq_one_in_neighborhood_gen (n : ℕ) (A : SL2C) (p : Fin n → Fin 4 → ℝ)
    (hp : p ∈ cutoffNeighborhood n A) :
    vladimirovCutoffBump n 1 Real.zero_lt_one p = 1 ∧
    vladimirovCutoffBump n 1 Real.zero_lt_one ((lorentzEquiv n A⁻¹) p) = 1 := by
  obtain ⟨h1, h2⟩ := hp
  rw [Set.mem_preimage] at h2
  refine ⟨vladimirov_cutoff_bump_one_of_mem_ball_gen n 1 le_rfl p h1,
          vladimirov_cutoff_bump_one_of_mem_ball_gen n 1 le_rfl ((lorentzEquiv n A⁻¹) p) h2⟩

lemma vladimirov_psi_eq_in_neighborhood_gen (n : ℕ) (A : SL2C)
    (z : Fin n → Fin 4 → ℂ) (p : Fin n → Fin 4 → ℝ)
    (hp : p ∈ cutoffNeighborhood n A) :
    vladimirov_psi n 1 Real.zero_lt_one (spinorPhi (A, sl2c_conj A) • z) p =
    vladimirov_psi n 1 Real.zero_lt_one z ((lorentzEquiv n A⁻¹) p) := by
  have ⟨h1, h2⟩ := cutoff_eq_one_in_neighborhood_gen n A p hp
  dsimp [vladimirov_psi]
  rw [h1, h2]
  push_cast
  rw [one_mul, one_mul]
  have h_inv := vladimirov_kernel_lorentz_inv n A z p
  rw [h_inv]
  rfl

lemma vladimirov_cutoff_bump_one_of_mem_ball (r : ℝ) (hr : r ≤ 1) (p : Fin 1 → Fin 4 → ℝ)
    (hp : p ∈ Metric.ball (0 : Fin 1 → Fin 4 → ℝ) r) :
    (vladimirovCutoffBump 1 1 Real.zero_lt_one p : ℝ) = 1 :=
  vladimirov_cutoff_bump_one_of_mem_ball_gen 1 r hr p hp

def cutoffNeighborhood_one (A : SL2C) : Set (Fin 1 → Fin 4 → ℝ) :=
  cutoffNeighborhood 1 A

lemma isOpen_cutoffNeighborhood_one (A : SL2C) :
    IsOpen (cutoffNeighborhood_one A) := by
  refine Metric.isOpen_ball.inter ?_
  exact (lorentzEquiv 1 A⁻¹).continuous.isOpen_preimage _ Metric.isOpen_ball

lemma spectralRegion_one_subset_cutoffNeighborhood (A : SL2C) :
    spectralRegion 1 ⊆ cutoffNeighborhood_one A := by
  intro p hp
  have hp0 : p = 0 := spectralRegion_one_eq_zero p hp
  subst hp0
  dsimp [cutoffNeighborhood_one]
  refine ⟨Metric.mem_ball_self Real.zero_lt_one, ?_⟩
  simp only [Set.mem_preimage, map_zero, Metric.mem_ball_self Real.zero_lt_one]

lemma cutoff_eq_one_in_neighborhood (A : SL2C) (p : Fin 1 → Fin 4 → ℝ)
    (hp : p ∈ cutoffNeighborhood_one A) :
    (vladimirovCutoffBump 1 1 Real.zero_lt_one p : ℝ) = 1 ∧
    (vladimirovCutoffBump 1 1 Real.zero_lt_one ((lorentzEquiv 1 A⁻¹) p) : ℝ) = 1 := by
  dsimp [cutoffNeighborhood_one] at hp
  cases hp with
  | intro hp1 hp2 =>
    refine ⟨vladimirov_cutoff_bump_one_of_mem_ball 1 le_rfl p hp1,
            vladimirov_cutoff_bump_one_of_mem_ball 1 le_rfl _ hp2⟩

noncomputable def posScaledMomentum (p : Fin 1 → Fin 4 → ℝ) : Fin 1 → Fin 4 → ℝ :=
  ((2 * Real.pi)⁻¹) • p

noncomputable def scaledMomentum (p : Fin 1 → Fin 4 → ℝ) : Fin 1 → Fin 4 → ℝ :=
  (- (2 * Real.pi)⁻¹) • p

noncomputable def posScaledMomentumN (n : ℕ) (p : Fin n → Fin 4 → ℝ) : Fin n → Fin 4 → ℝ :=
  ((2 * Real.pi)⁻¹) • p

noncomputable def scaledMomentumN (n : ℕ) (p : Fin n → Fin 4 → ℝ) : Fin n → Fin 4 → ℝ :=
  (- (2 * Real.pi)⁻¹) • p

lemma norm_scaledMomentum (p : Fin 1 → Fin 4 → ℝ) :
    ‖scaledMomentum p‖ ≤ (2 * Real.pi)⁻¹ * ‖p‖ := by
  dsimp [scaledMomentum]
  rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_inv]
  have hpi : 0 < 2 * Real.pi := by positivity
  rw [abs_of_pos hpi]

lemma norm_scaledMomentumN (n : ℕ) (p : Fin n → Fin 4 → ℝ) :
    ‖scaledMomentumN n p‖ ≤ (2 * Real.pi)⁻¹ * ‖p‖ := by
  dsimp [scaledMomentumN]
  rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_inv]
  have hpi : 0 < 2 * Real.pi := by positivity
  rw [abs_of_pos hpi]

lemma continuous_scaledMomentumN (n : ℕ) : Continuous (scaledMomentumN n) := by
  change Continuous (fun p => (- (2 * Real.pi)⁻¹) • p)
  exact continuous_const_smul _

def scaledComNeighborhood (n : ℕ) (A : SL2C) (R : ℝ) : Set (Fin n → Fin 4 → ℝ) :=
  (scaledMomentumN n) ⁻¹' (comNeighborhood n A R)

lemma isOpen_scaledComNeighborhood (n : ℕ) (A : SL2C) (R : ℝ) :
    IsOpen (scaledComNeighborhood n A R) :=
  (isOpen_comNeighborhood n A R).preimage (continuous_scaledMomentumN n)

lemma spectralRegion_subset_scaledComNeighborhood (n : ℕ) (A : SL2C) (R : ℝ) (hR : 0 < R) :
    spectralRegion n ⊆ scaledComNeighborhood n A R := by
  intro p hp
  rw [scaledComNeighborhood, Set.mem_preimage]
  have hp0 : p = 0 := hp.2.2
  subst hp0
  have h_scaled : scaledMomentumN n 0 = 0 := smul_zero _
  rw [h_scaled]
  exact spectralRegion_subset_comNeighborhood n A R hR hp

lemma scaledMomentum_lt_one (p : Fin 1 → Fin 4 → ℝ) (hp : ‖p‖ < 1) :
    ‖scaledMomentum p‖ < 1 := by
  have h_bound := norm_scaledMomentum p
  have hpi : 1 < 2 * Real.pi := by
    have := Real.pi_gt_three
    linarith
  have h_inv : (2 * Real.pi)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hpi
  have h_prod : (2 * Real.pi)⁻¹ * ‖p‖ < 1 := by
    have h_inv_pos : 0 < (2 * Real.pi)⁻¹ := by positivity
    calc (2 * Real.pi)⁻¹ * ‖p‖ < (2 * Real.pi)⁻¹ * 1 := mul_lt_mul_of_pos_left hp h_inv_pos
    _ = (2 * Real.pi)⁻¹ := mul_one _
    _ < 1 := h_inv
  exact h_bound.trans_lt h_prod

lemma scaledMomentum_lorentz (A : SL2C) (p : Fin 1 → Fin 4 → ℝ) :
    scaledMomentum ((lorentzEquiv 1 A⁻¹) p) = (lorentzEquiv 1 A⁻¹) (scaledMomentum p) := by
  dsimp [scaledMomentum]
  exact ((lorentzEquiv 1 A⁻¹).toLinearMap.map_smul (- (2 * Real.pi)⁻¹) p).symm

lemma scaledMomentum_mem_neighborhood (A : SL2C) (p : Fin 1 → Fin 4 → ℝ)
    (hp : p ∈ cutoffNeighborhood_one A) :
    scaledMomentum p ∈ cutoffNeighborhood_one A := by
  obtain ⟨hp1, hp2⟩ := hp
  rw [Metric.mem_ball, dist_zero_right] at hp1
  refine ⟨?_, ?_⟩
  · rw [Metric.mem_ball, dist_zero_right]
    exact scaledMomentum_lt_one p hp1
  · rw [Set.mem_preimage, Metric.mem_ball, dist_zero_right] at hp2 ⊢
    rw [← scaledMomentum_lorentz]
    exact scaledMomentum_lt_one _ hp2

lemma vladimirov_psi_eq_in_neighborhood (A : SL2C) (z : Fin 1 → Fin 4 → ℂ) (p : Fin 1 → Fin 4 → ℝ)
    (hp : p ∈ cutoffNeighborhood_one A) :
    vladimirov_psi 1 1 Real.zero_lt_one (spinorPhi (A, sl2c_conj A) • z) p =
    vladimirov_psi 1 1 Real.zero_lt_one z ((lorentzEquiv 1 A⁻¹) p) := by
  have ⟨h1, h2⟩ := cutoff_eq_one_in_neighborhood A p hp
  dsimp [vladimirov_psi]
  rw [h1, h2]
  push_cast
  rw [one_mul, one_mul]
  have h_inv := vladimirov_kernel_lorentz_inv 1 A z p
  rw [h_inv]
  rfl

lemma minkowskiFourier_schwartzLorentzCLM_n (n : ℕ) (A : SL2C)
    (g : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) (p : Fin n → Fin 4 → ℝ) :
    minkowskiFourier (schwartzLorentzCLM n A⁻¹ g) p =
    minkowskiFourier g ((lorentzEquiv n A⁻¹) p) := by
  dsimp [minkowskiFourier]
  have h_meas : MeasurePreserving (lorentzEquiv n A) volume volume :=
    measurePreserving_lorentzEquiv_n n A
  have h_emb : MeasurableEmbedding (lorentzEquiv n A) :=
    (lorentzEquiv n A).toHomeomorph.measurableEmbedding
  have h_comp := (MeasurePreserving.integral_comp h_meas h_emb
    (fun x => (schwartzLorentzCLM n A⁻¹ g) x *
      Complex.exp (-(Complex.I * ((∑ k, minkowskiInner (p k) (x k) : ℝ) : ℂ))))).symm
  rw [h_comp]
  have h_eq : ∀ x : Fin n → Fin 4 → ℝ,
      (schwartzLorentzCLM n A⁻¹ g) ((lorentzEquiv n A) x) *
        Complex.exp (-(Complex.I *
          ((∑ k, minkowskiInner (p k) (((lorentzEquiv n A) x) k) : ℝ) : ℂ))) =
      g x * Complex.exp (-(Complex.I *
        ((∑ k, minkowskiInner (((lorentzEquiv n A⁻¹) p) k) (x k) : ℝ) : ℂ))) := by
    intro x
    have h_rel : (schwartzLorentzCLM n A⁻¹ g) ((lorentzEquiv n A) x) = g x := by
      exact schwartzLorentz_rel n A g x
    rw [h_rel]
    congr 1
    have h_sum : (∑ k : Fin n, minkowskiInner (p k) (((lorentzEquiv n A) x) k)) =
                 (∑ k : Fin n, minkowskiInner (((lorentzEquiv n A⁻¹) p) k) (x k)) := by
      exact sum_minkowskiInner_lorentz_pair n A p x
    rw [h_sum]
  simp_rw [h_eq]

lemma minkowskiFourier_schwartzLorentzCLM_one (A : SL2C)
    (g : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) (p : Fin 1 → Fin 4 → ℝ) :
    minkowskiFourier (schwartzLorentzCLM 1 A⁻¹ g) p =
    minkowskiFourier g ((lorentzEquiv 1 A⁻¹) p) :=
  minkowskiFourier_schwartzLorentzCLM_n 1 A g p

lemma inner_piSpaceEquiv_minkowskiFlip_n (n : ℕ) (p x : Fin n → Fin 4 → ℝ) :
    inner ℝ (piSpaceEquiv n (minkowskiFlipFun n x)) (piSpaceEquiv n p) =
    ∑ k : Fin n, minkowskiInner (p k) (x k) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [star_trivial, dotProduct]
  change (∑ i : Fin n × Fin 4, p i.1 i.2 * (if i.2 = 0 then x i.1 0 else -x i.1 i.2)) = _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro k _
  rw [Fin.sum_univ_four]
  dsimp
  rw [minkowskiInner_explicit]
  ring

lemma inner_piSpaceEquiv_minkowskiFlip (p x : Fin 1 → Fin 4 → ℝ) :
    inner ℝ (piSpaceEquiv 1 (minkowskiFlipFun 1 x)) (piSpaceEquiv 1 p) =
    minkowskiInner (p 0) (x 0) := by
  have h := inner_piSpaceEquiv_minkowskiFlip_n 1 p x
  rw [Fin.sum_univ_one] at h
  exact h

lemma fourier_phase_eq_n (n : ℕ) (p x : Fin n → Fin 4 → ℝ) :
    (-2 * Real.pi * inner ℝ (piSpaceEquiv n (minkowskiFlipFun n x))
        (piSpaceEquiv n (posScaledMomentumN n p))) =
    - ∑ k : Fin n, minkowskiInner (p k) (x k) := by
  dsimp [posScaledMomentumN]
  rw [map_smul, real_inner_smul_right]
  have hpi : 2 * Real.pi ≠ 0 := by
    have := Real.pi_pos
    positivity
  have h_inner := inner_piSpaceEquiv_minkowskiFlip_n n p x
  rw [h_inner]
  have h_cancel : -2 * Real.pi * ((2 * Real.pi)⁻¹ * ∑ k : Fin n, minkowskiInner (p k) (x k)) =
      - (2 * Real.pi * (2 * Real.pi)⁻¹) * ∑ k : Fin n, minkowskiInner (p k) (x k) := by ring
  rw [h_cancel, mul_inv_cancel₀ hpi]
  ring

lemma fourier_phase_eq (p x : Fin 1 → Fin 4 → ℝ) :
    (-2 * Real.pi * inner ℝ (piSpaceEquiv 1 (minkowskiFlipFun 1 x))
        (piSpaceEquiv 1 (posScaledMomentum p))) =
    - minkowskiInner (p 0) (x 0) := by
  dsimp [posScaledMomentum]
  rw [map_smul, real_inner_smul_right]
  have hpi : 2 * Real.pi ≠ 0 := by
    have := Real.pi_pos
    positivity
  have h_inner := inner_piSpaceEquiv_minkowskiFlip p x
  rw [h_inner]
  have h_cancel : -2 * Real.pi * ((2 * Real.pi)⁻¹ * minkowskiInner (p 0) (x 0)) =
      - (2 * Real.pi * (2 * Real.pi)⁻¹) * minkowskiInner (p 0) (x 0) := by ring
  rw [h_cancel, mul_inv_cancel₀ hpi]
  ring

lemma fourier_fourier_apply {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (f : SchwartzMap V ℂ) (y : V) :
    𝓕 (𝓕 (f : V → ℂ)) (-y) = f y := by
  have h_inv : (𝓕⁻ (𝓕 f) : SchwartzMap V ℂ) = f := FourierPair.fourierInv_fourier_eq f
  have h_apply : ((𝓕⁻ (𝓕 f) : SchwartzMap V ℂ) : V → ℂ) y = f y := by
    rw [h_inv]
  have h_coe : ((𝓕⁻ (𝓕 f) : SchwartzMap V ℂ) : V → ℂ) y = 𝓕 (𝓕 (f : V → ℂ)) (-y) := by
    have h1 : ((𝓕⁻ (𝓕 f) : SchwartzMap V ℂ) : V → ℂ) = 𝓕⁻ ((𝓕 f : SchwartzMap V ℂ) : V → ℂ) :=
      SchwartzMap.fourierInv_coe (𝓕 f)
    have h2 : 𝓕⁻ ((𝓕 f : SchwartzMap V ℂ) : V → ℂ) y = 𝓕 ((𝓕 f : SchwartzMap V ℂ) : V → ℂ) (-y) :=
      Real.fourierInv_eq_fourier_neg ((𝓕 f : SchwartzMap V ℂ) : V → ℂ) y
    have h3 : ((𝓕 f : SchwartzMap V ℂ) : V → ℂ) = 𝓕 (f : V → ℂ) :=
      SchwartzMap.fourier_coe f
    rw [congr_fun h1 y, h2, h3]
  rw [h_coe] at h_apply
  exact h_apply

lemma invMinkowskiFourierCLM_apply_one (g : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ)
    (x : Fin 1 → Fin 4 → ℝ) :
    (invMinkowskiFourierCLM 1 g) x =
    𝓕 (⇑g ∘ ⇑(piSpaceEquiv 1).symm) (piSpaceEquiv 1 (minkowskiFlipFun 1 x)) := rfl

lemma measurePreserving_refl :
    MeasurePreserving (MeasurableEquiv.refl ℝ) volume volume :=
  ⟨measurable_id, Measure.map_id⟩

lemma measurePreserving_finCurryEquiv_one :
    MeasurePreserving (finCurryEquiv 1) volume volume := by
  let e_prod : (Fin 1 × Fin 4) ≃ Fin 4 := {
    toFun := fun ⟨_, k⟩ => k
    invFun := fun k => (0, k)
    left_inv := fun ⟨i, k⟩ => by
      have hi : i = 0 := Subsingleton.elim i 0
      subst hi; rfl
    right_inv := fun k => rfl
  }
  have h_meas : MeasurePreserving
      (MeasurableEquiv.arrowCongr' e_prod (MeasurableEquiv.refl ℝ)) volume volume :=
    volume_preserving_arrowCongr' e_prod (MeasurableEquiv.refl ℝ) measurePreserving_refl
  have h_fun : MeasurePreserving (MeasurableEquiv.funUnique (Fin 1) (Fin 4 → ℝ)) volume volume :=
    volume_preserving_funUnique (Fin 1) (Fin 4 → ℝ)
  have h_comp : MeasurePreserving ((MeasurableEquiv.funUnique (Fin 1) (Fin 4 → ℝ)).trans
      (MeasurableEquiv.arrowCongr' e_prod (MeasurableEquiv.refl ℝ)).symm) volume volume :=
    h_meas.symm.comp h_fun
  have h_eq : ⇑(finCurryEquiv 1) = ⇑((MeasurableEquiv.funUnique (Fin 1) (Fin 4 → ℝ)).trans
      (MeasurableEquiv.arrowCongr' e_prod (MeasurableEquiv.refl ℝ)).symm) := by
    ext f ⟨i, k⟩
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    rfl
  rw [h_eq]
  exact h_comp

lemma measurePreserving_finEuclidEquiv_one :
    MeasurePreserving (finEuclidEquiv 1) volume volume := by
  dsimp [finEuclidEquiv]
  exact PiLp.volume_preserving_toLp (Fin 1 × Fin 4)

lemma measurePreserving_piSpaceEquiv_one :
    MeasurePreserving (piSpaceEquiv 1) volume volume := by
  dsimp [piSpaceEquiv]
  exact measurePreserving_finEuclidEquiv_one.comp measurePreserving_finCurryEquiv_one

lemma abs_det_minkowskiFlip_n (n : ℕ) :
    |LinearMap.det (minkowskiFlipEquiv n).toLinearMap| = 1 := by
  have h_comp : (minkowskiFlipEquiv n).toLinearMap.comp (minkowskiFlipEquiv n).toLinearMap =
      LinearMap.id := by
    apply LinearMap.ext
    intro x
    exact minkowskiFlipFun_involutive n x
  have h_det := congr_arg LinearMap.det h_comp
  rw [LinearMap.det_comp, LinearMap.det_id] at h_det
  rcases mul_self_eq_one_iff.mp h_det with h | h
  · rw [h, abs_one]
  · rw [h, abs_neg, abs_one]

lemma abs_det_minkowskiFlip_one :
    |LinearMap.det (minkowskiFlipEquiv 1).toLinearMap| = 1 :=
  abs_det_minkowskiFlip_n 1

lemma measurePreserving_minkowskiFlip_n (n : ℕ) :
    MeasurePreserving (minkowskiFlipEquiv n) volume volume := by
  have h_abs := abs_det_minkowskiFlip_n n
  have h_det_ne : LinearMap.det (minkowskiFlipEquiv n).toLinearMap ≠ 0 := by
    intro hz
    rw [hz, abs_zero] at h_abs
    exact zero_ne_one h_abs
  have h_map := Measure.map_linearMap_addHaar_eq_smul_addHaar volume h_det_ne
  rw [abs_inv, h_abs, inv_one, ENNReal.ofReal_one, one_smul] at h_map
  exact ⟨(minkowskiFlipEquiv n).continuous.measurable, h_map⟩

lemma measurePreserving_minkowskiFlip_one :
    MeasurePreserving (minkowskiFlipEquiv 1) volume volume :=
  measurePreserving_minkowskiFlip_n 1

lemma measurePreserving_minkowskiFlip_piSpace_one :
    MeasurePreserving
      (fun x : Fin 1 → Fin 4 → ℝ => piSpaceEquiv 1 (minkowskiFlipFun 1 x)) volume volume := by
  have h_comp : (fun x : Fin 1 → Fin 4 → ℝ => piSpaceEquiv 1 (minkowskiFlipFun 1 x)) =
      (piSpaceEquiv 1) ∘ (minkowskiFlipEquiv 1) := rfl
  rw [h_comp]
  exact measurePreserving_piSpaceEquiv_one.comp measurePreserving_minkowskiFlip_one

noncomputable def minkowskiFlip_piSpace_homeomorph_n (n : ℕ) :
    (Fin n → Fin 4 → ℝ) ≃ₜ EuclideanSpace ℝ (Fin n × Fin 4) :=
  (minkowskiFlipEquiv n).toHomeomorph.trans (piSpaceEquiv n).toHomeomorph

lemma coe_minkowskiFlip_piSpace_homeomorph_n (n : ℕ) :
    ⇑(minkowskiFlip_piSpace_homeomorph_n n) = fun x => piSpaceEquiv n (minkowskiFlipFun n x) := rfl

lemma measurableEmbedding_minkowskiFlip_piSpace_n (n : ℕ) :
    MeasurableEmbedding (fun x : Fin n → Fin 4 → ℝ => piSpaceEquiv n (minkowskiFlipFun n x)) := by
  rw [← coe_minkowskiFlip_piSpace_homeomorph_n n]
  exact (minkowskiFlip_piSpace_homeomorph_n n).measurableEmbedding

noncomputable def minkowskiFlip_piSpace_homeomorph_one :
    (Fin 1 → Fin 4 → ℝ) ≃ₜ EuclideanSpace ℝ (Fin 1 × Fin 4) :=
  minkowskiFlip_piSpace_homeomorph_n 1

lemma coe_minkowskiFlip_piSpace_homeomorph_one :
    ⇑minkowskiFlip_piSpace_homeomorph_one = fun x => piSpaceEquiv 1 (minkowskiFlipFun 1 x) := rfl

lemma measurableEmbedding_minkowskiFlip_piSpace_one :
    MeasurableEmbedding (fun x : Fin 1 → Fin 4 → ℝ => piSpaceEquiv 1 (minkowskiFlipFun 1 x)) :=
  measurableEmbedding_minkowskiFlip_piSpace_n 1

lemma minkowskiFourier_invMinkowskiFourierCLM_n (n : ℕ)
    (g : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) (p : Fin n → Fin 4 → ℝ)
    (h_meas : MeasurePreserving
      (fun x : Fin n → Fin 4 → ℝ => piSpaceEquiv n (minkowskiFlipFun n x)) volume volume) :
    minkowskiFourier (invMinkowskiFourierCLM n g) p = g (scaledMomentumN n p) := by
  dsimp [minkowskiFourier]
  have h_emb := measurableEmbedding_minkowskiFlip_piSpace_n n
  have h_comp := (MeasurePreserving.integral_comp h_meas h_emb
    (fun u : EuclideanSpace ℝ (Fin n × Fin 4) =>
      𝓕 (⇑g ∘ ⇑(piSpaceEquiv n).symm) u *
        Complex.exp ((-2 * Real.pi *
          inner ℝ u (piSpaceEquiv n (posScaledMomentumN n p)) : ℝ) * Complex.I))).symm
  have h_integrand : (fun x : Fin n → Fin 4 → ℝ =>
      (invMinkowskiFourierCLM n g) x *
        Complex.exp (-(Complex.I * ((∑ k : Fin n, minkowskiInner (p k) (x k) : ℝ) : ℂ)))) =
      (fun x =>
        (fun u => 𝓕 (⇑g ∘ ⇑(piSpaceEquiv n).symm) u *
          Complex.exp ((-2 * Real.pi *
            inner ℝ u (piSpaceEquiv n (posScaledMomentumN n p)) : ℝ) * Complex.I))
            (piSpaceEquiv n (minkowskiFlipFun n x))) := by
    ext x
    dsimp
    have h_eval : (invMinkowskiFourierCLM n g) x =
        𝓕 (⇑g ∘ ⇑(piSpaceEquiv n).symm) (piSpaceEquiv n (minkowskiFlipFun n x)) := rfl
    rw [h_eval]
    congr 1
    have h_phase := fourier_phase_eq_n n p x
    have h_eq : -(Complex.I * ((∑ k, minkowskiInner (p k) (x k) : ℝ) : ℂ)) =
        (((-2 * Real.pi * inner ℝ (piSpaceEquiv n (minkowskiFlipFun n x))
          (piSpaceEquiv n (posScaledMomentumN n p)) : ℝ) : ℂ) * Complex.I) := by
      rw [h_phase]
      push_cast
      ring
    rw [h_eq]
  rw [h_integrand, ← h_comp]
  have h_fourier : (fun u : EuclideanSpace ℝ (Fin n × Fin 4) =>
      𝓕 (⇑g ∘ ⇑(piSpaceEquiv n).symm) u *
        Complex.exp ((-2 * Real.pi *
          inner ℝ u (piSpaceEquiv n (posScaledMomentumN n p)) : ℝ) * Complex.I)) =
      (fun u => 𝓕 (⇑g ∘ ⇑(piSpaceEquiv n).symm) u *
        Complex.exp (↑(2 * Real.pi *
          (- inner ℝ u (piSpaceEquiv n (posScaledMomentumN n p)))) * Complex.I)) := by
    ext u
    congr 2
    have : (-2 * Real.pi * inner ℝ u (piSpaceEquiv n (posScaledMomentumN n p))) =
        (2 * Real.pi * (- inner ℝ u (piSpaceEquiv n (posScaledMomentumN n p)))) := by ring
    rw [this]
  rw [h_fourier]
  have h_double : (∫ u, 𝓕 (⇑g ∘ ⇑(piSpaceEquiv n).symm) u *
      Complex.exp (↑(2 * Real.pi *
        (- inner ℝ u (piSpaceEquiv n (posScaledMomentumN n p)))) * Complex.I)) =
      𝓕 (𝓕 (⇑g ∘ ⇑(piSpaceEquiv n).symm)) (piSpaceEquiv n (posScaledMomentumN n p)) := by
    rw [Real.fourier_eq]
    congr 1
    ext u
    simp only [Circle.smul_def, Real.fourierChar_apply]
    ring
  rw [h_double]
  let h_schwartz : SchwartzMap (EuclideanSpace ℝ (Fin n × Fin 4)) ℂ :=
    (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (piSpaceEquiv n).symm) g
  have h_coe : ⇑g ∘ ⇑(piSpaceEquiv n).symm = (h_schwartz : _ → ℂ) := rfl
  rw [h_coe]
  have h_eval := fourier_fourier_apply h_schwartz (- (piSpaceEquiv n (posScaledMomentumN n p)))
  rw [neg_neg] at h_eval
  rw [h_eval]
  have h_symm : (piSpaceEquiv n).symm (- (piSpaceEquiv n (posScaledMomentumN n p))) =
      scaledMomentumN n p := by
    rw [← map_neg, (piSpaceEquiv n).symm_apply_apply]
    dsimp [posScaledMomentumN, scaledMomentumN]
    rw [neg_smul]
  exact congr_arg g h_symm

lemma minkowskiFourier_invMinkowskiFourierCLM_one (g : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ)
    (p : Fin 1 → Fin 4 → ℝ) :
    minkowskiFourier (invMinkowskiFourierCLM 1 g) p = g (scaledMomentum p) := by
  exact minkowskiFourier_invMinkowskiFourierCLM_n 1 g p
    measurePreserving_minkowskiFlip_piSpace_one

lemma measurePreserving_finEuclidEquiv_n (n : ℕ) :
    MeasurePreserving (finEuclidEquiv n) volume volume := by
  dsimp [finEuclidEquiv]
  exact PiLp.volume_preserving_toLp (Fin n × Fin 4)

lemma measurePreserving_finCurryEquiv_n (n : ℕ) :
    MeasurePreserving (finCurryEquiv n) volume volume := by
  have h_meas : Measurable (finCurryEquiv n) := (finCurryEquiv n).continuous.measurable
  refine ⟨h_meas, ?_⟩
  refine (Measure.pi_eq fun s hs => ?_).symm
  have h_preimage : (finCurryEquiv n) ⁻¹' (Set.pi Set.univ s) =
      Set.pi Set.univ (fun i => Set.pi Set.univ (fun k => s (i, k))) := by
    ext f
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left]
    dsimp [finCurryEquiv]
    constructor
    · intro h i k
      exact h (i, k)
    · intro h ⟨i, k⟩
      exact h i k
  rw [Measure.map_apply h_meas (MeasurableSet.univ_pi hs), h_preimage]
  rw [volume_pi, Measure.pi_pi]
  have h_inner (i : Fin n) :
      (volume : Measure (Fin 4 → ℝ)) (Set.pi Set.univ (fun k => s (i, k))) =
      ∏ k : Fin 4, volume (s (i, k)) := by
    rw [volume_pi, Measure.pi_pi]
  simp_rw [h_inner]
  exact (Fintype.prod_prod_type (fun p : Fin n × Fin 4 => volume (s p))).symm

lemma measurePreserving_piSpaceEquiv_n (n : ℕ) :
    MeasurePreserving (piSpaceEquiv n) volume volume := by
  dsimp [piSpaceEquiv]
  exact (measurePreserving_finEuclidEquiv_n n).comp (measurePreserving_finCurryEquiv_n n)

lemma measurePreserving_minkowskiFlip_piSpace_n (n : ℕ) :
    MeasurePreserving
      (fun x : Fin n → Fin 4 → ℝ => piSpaceEquiv n (minkowskiFlipFun n x)) volume volume := by
  have h_comp : (fun x : Fin n → Fin 4 → ℝ => piSpaceEquiv n (minkowskiFlipFun n x)) =
      (piSpaceEquiv n) ∘ (minkowskiFlipEquiv n) := rfl
  rw [h_comp]
  exact (measurePreserving_piSpaceEquiv_n n).comp (measurePreserving_minkowskiFlip_n n)

lemma minkowskiFourier_invMinkowskiFourierCLM_all (n : ℕ)
    (g : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) (p : Fin n → Fin 4 → ℝ) :
    minkowskiFourier (invMinkowskiFourierCLM n g) p = g (scaledMomentumN n p) :=
  minkowskiFourier_invMinkowskiFourierCLM_n n g p (measurePreserving_minkowskiFlip_piSpace_n n)

lemma minkowskiFourier_cutoff_lorentz_diff_n1 (A : SL2C) (z : Fin 1 → Fin 4 → ℂ) :
    ∃ U : Set (Fin 1 → Fin 4 → ℝ), IsOpen U ∧ spectralRegion 1 ⊆ U ∧
      ∀ p ∈ U, minkowskiFourier
        (invMinkowskiFourierCLM 1
          (vladimirov_psi_schwartz 1 1 Real.zero_lt_one (spinorPhi (A, sl2c_conj A) • z)) -
         schwartzLorentzCLM 1 A⁻¹
          (invMinkowskiFourierCLM 1 (vladimirov_psi_schwartz 1 1 Real.zero_lt_one z))) p = 0 := by
  refine ⟨cutoffNeighborhood_one A, isOpen_cutoffNeighborhood_one A,
          spectralRegion_one_subset_cutoffNeighborhood A, ?_⟩
  intro p hp
  rw [minkowskiFourier_sub]
  rw [minkowskiFourier_schwartzLorentzCLM_one]
  rw [minkowskiFourier_invMinkowskiFourierCLM_one]
  rw [minkowskiFourier_invMinkowskiFourierCLM_one]
  have h_lorentz := scaledMomentum_lorentz A p
  rw [h_lorentz]
  have h_mem := scaledMomentum_mem_neighborhood A p hp
  have h_eq := vladimirov_psi_eq_in_neighborhood A z (scaledMomentum p) h_mem
  change (vladimirov_psi 1 1 Real.zero_lt_one (spinorPhi (A, sl2c_conj A) • z) (scaledMomentum p)) -
         (vladimirov_psi 1 1 Real.zero_lt_one z ((lorentzEquiv 1 A⁻¹) (scaledMomentum p))) = 0
  rw [h_eq, sub_self]

lemma scaledMomentumN_lorentz (n : ℕ) (A : SL2C) (p : Fin n → Fin 4 → ℝ) :
    scaledMomentumN n ((lorentzEquiv n A⁻¹) p) = (lorentzEquiv n A⁻¹) (scaledMomentumN n p) := by
  dsimp [scaledMomentumN]
  exact ((lorentzEquiv n A⁻¹).map_smul (- (2 * Real.pi)⁻¹) p).symm

lemma minkowskiFourier_eval_diff (n : ℕ) (A : SL2C) (z : Fin n → Fin 4 → ℂ)
    (p : Fin n → Fin 4 → ℝ) (hp : scaledMomentumN n p ∈ cutoffNeighborhood n A) :
    minkowskiFourier
      (invMinkowskiFourierCLM n
        (vladimirov_psi_schwartz n 1 Real.zero_lt_one (spinorPhi (A, sl2c_conj A) • z)) -
       schwartzLorentzCLM n A⁻¹
        (invMinkowskiFourierCLM n (vladimirov_psi_schwartz n 1 Real.zero_lt_one z))) p = 0 := by
  rw [minkowskiFourier_sub]
  rw [minkowskiFourier_schwartzLorentzCLM_n]
  rw [minkowskiFourier_invMinkowskiFourierCLM_all]
  rw [minkowskiFourier_invMinkowskiFourierCLM_all]
  have h_lorentz := scaledMomentumN_lorentz n A p
  rw [h_lorentz]
  have h_eq := vladimirov_psi_eq_in_neighborhood_gen n A z (scaledMomentumN n p) hp
  change (vladimirov_psi n 1 Real.zero_lt_one (spinorPhi (A, sl2c_conj A) • z)
           (scaledMomentumN n p)) -
         (vladimirov_psi n 1 Real.zero_lt_one z
           ((lorentzEquiv n A⁻¹) (scaledMomentumN n p))) = 0
  rw [h_eq, sub_self]

def totalCutoffNeighborhood (n : ℕ) (A : SL2C) : Set (Fin n → Fin 4 → ℝ) :=
  { p | (fun _ : Fin 1 => total_momentum_LM n p) ∈ cutoffNeighborhood 1 A }

lemma isOpen_totalCutoffNeighborhood (n : ℕ) (A : SL2C) :
    IsOpen (totalCutoffNeighborhood n A) := by
  let phi : (Fin n → Fin 4 → ℝ) →L[ℝ] (Fin 1 → Fin 4 → ℝ) :=
    ContinuousLinearMap.pi (fun _ => total_momentum_CLM n)
  have h_eq : totalCutoffNeighborhood n A = phi ⁻¹' (cutoffNeighborhood 1 A) := by
    ext p; rfl
  rw [h_eq]
  exact (isOpen_cutoffNeighborhood 1 A).preimage phi.continuous

lemma spectralRegion_subset_totalCutoffNeighborhood (n : ℕ) (A : SL2C) :
    spectralRegion n ⊆ totalCutoffNeighborhood n A := by
  intro p hp
  dsimp [totalCutoffNeighborhood]
  have hp0 := total_momentum_eq_zero_of_mem_spectralRegion n p hp
  have h_fun_zero : (fun _ : Fin 1 => total_momentum_LM n p) = 0 := by
    ext i; rw [hp0]; rfl
  rw [h_fun_zero]
  dsimp [cutoffNeighborhood]
  refine ⟨Metric.mem_ball_self Real.zero_lt_one, ?_⟩
  simp only [Set.mem_preimage, map_zero, Metric.mem_ball_self Real.zero_lt_one]

lemma minkowskiFourier_cutoff_lorentz_diff (n : ℕ) (hn : n ≤ 1) (A : SL2C) (z : Fin n → Fin 4 → ℂ) :
    ∃ U : Set (Fin n → Fin 4 → ℝ), IsOpen U ∧ spectralRegion n ⊆ U ∧
      ∀ p ∈ U, minkowskiFourier
        (invMinkowskiFourierCLM n
          (vladimirov_psi_schwartz n 1 Real.zero_lt_one (spinorPhi (A, sl2c_conj A) • z)) -
         schwartzLorentzCLM n A⁻¹
          (invMinkowskiFourierCLM n (vladimirov_psi_schwartz n 1 Real.zero_lt_one z))) p = 0 := by
  interval_cases n
  · exact minkowskiFourier_cutoff_lorentz_diff_n0 A z
  · exact minkowskiFourier_cutoff_lorentz_diff_n1 A z

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_cutoff_lorentz_diff_zero (W : WightmanFamily ι)
    (A : SL2C) (z : Fin 0 → Fin 4 → ℂ) (α : Fin 0 → ι) :
    W 0 α (invMinkowskiFourierCLM 0
      (vladimirov_psi_schwartz 0 1 Real.zero_lt_one (spinorPhi (A, sl2c_conj A) • z))) =
    W 0 α (schwartzLorentzCLM 0 A⁻¹
      (invMinkowskiFourierCLM 0 (vladimirov_psi_schwartz 0 1 Real.zero_lt_one z))) := by
  have h_phi : (spinorPhi (A, sl2c_conj A) • z) = z := spinorPhi_smul_zero A z
  rw [h_phi]
  have h_clm : schwartzLorentzCLM 0 A⁻¹ = ContinuousLinearMap.id ℂ _ := schwartzLorentzCLM_zero A⁻¹
  rw [h_clm, ContinuousLinearMap.id_apply]

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_cutoff_lorentz_diff_of_vanish (W : WightmanFamily ι) (hspec : SpectrumCondition W)
    (n : ℕ) (A : SL2C) (z : Fin n → Fin 4 → ℂ) (α : Fin n → ι)
    (h_diff : ∃ U : Set (Fin n → Fin 4 → ℝ), IsOpen U ∧ spectralRegion n ⊆ U ∧
      ∀ p ∈ U, minkowskiFourier
        (invMinkowskiFourierCLM n
          (vladimirov_psi_schwartz n 1 Real.zero_lt_one (spinorPhi (A, sl2c_conj A) • z)) -
         schwartzLorentzCLM n A⁻¹
          (invMinkowskiFourierCLM n (vladimirov_psi_schwartz n 1 Real.zero_lt_one z))) p = 0) :
    W n α (invMinkowskiFourierCLM n
      (vladimirov_psi_schwartz n 1 Real.zero_lt_one (spinorPhi (A, sl2c_conj A) • z))) =
    W n α (schwartzLorentzCLM n A⁻¹
      (invMinkowskiFourierCLM n (vladimirov_psi_schwartz n 1 Real.zero_lt_one z))) := by
  let f1 := invMinkowskiFourierCLM n
    (vladimirov_psi_schwartz n 1 Real.zero_lt_one (spinorPhi (A, sl2c_conj A) • z))
  let f2 := schwartzLorentzCLM n A⁻¹
    (invMinkowskiFourierCLM n (vladimirov_psi_schwartz n 1 Real.zero_lt_one z))
  have h_sub : W n α f1 - W n α f2 = W n α (f1 - f2) := by rw [map_sub]
  suffices h_zero : W n α (f1 - f2) = 0 by
    rw [← sub_eq_zero, h_sub, h_zero]
  exact hspec n α (f1 - f2) (Or.inl h_diff)

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_cutoff_lorentz_diff (W : WightmanFamily ι) (hspec : SpectrumCondition W)
    (n : ℕ) (hn : n ≤ 1) (A : SL2C) (z : Fin n → Fin 4 → ℂ) (α : Fin n → ι) :
    W n α (invMinkowskiFourierCLM n
      (vladimirov_psi_schwartz n 1 Real.zero_lt_one (spinorPhi (A, sl2c_conj A) • z))) =
    W n α (schwartzLorentzCLM n A⁻¹
      (invMinkowskiFourierCLM n (vladimirov_psi_schwartz n 1 Real.zero_lt_one z))) := by
  interval_cases n
  · exact vladimirov_cutoff_lorentz_diff_zero W A z α
  · let f1 := invMinkowskiFourierCLM 1
      (vladimirov_psi_schwartz 1 1 Real.zero_lt_one (spinorPhi (A, sl2c_conj A) • z))
    let f2 := schwartzLorentzCLM 1 A⁻¹
      (invMinkowskiFourierCLM 1 (vladimirov_psi_schwartz 1 1 Real.zero_lt_one z))
    have h_sub : W 1 α f1 - W 1 α f2 = W 1 α (f1 - f2) := by rw [map_sub]
    suffices h_zero : W 1 α (f1 - f2) = 0 by
      rw [← sub_eq_zero, h_sub, h_zero]
    apply hspec 1 α (f1 - f2)
    exact Or.inl (minkowskiFourier_cutoff_lorentz_diff 1 le_rfl A z)

lemma minkowskiInner_comm (x y : Fin 4 → ℝ) : minkowskiInner x y = minkowskiInner y x := by
  simp only [minkowskiInner_explicit]
  ring

lemma test_phase_cancel_inv (p a : Fin 1 → Fin 4 → ℝ) :
    (Real.fourierChar (inner ℝ (piSpaceEquiv 1 (posScaledMomentum a))
      (piSpaceEquiv 1 (minkowskiFlipFun 1 p))) : ℂ) =
    Complex.exp (Complex.I * (minkowskiInner (a 0) (p 0) : ℂ)) := by
  rw [Real.fourierChar_apply]
  have hpi : 2 * Real.pi ≠ 0 := by
    have := Real.pi_pos
    positivity
  have h_inner : inner ℝ (piSpaceEquiv 1 (posScaledMomentum a))
      (piSpaceEquiv 1 (minkowskiFlipFun 1 p)) =
      (2 * Real.pi)⁻¹ * minkowskiInner (a 0) (p 0) := by
    dsimp [posScaledMomentum]
    rw [map_smul, real_inner_smul_left]
    rw [real_inner_comm]
    have h1 := inner_piSpaceEquiv_minkowskiFlip a p
    rw [h1]
  rw [h_inner]
  have h_mul : ↑(2 * Real.pi * ((2 * Real.pi)⁻¹ * minkowskiInner (a 0) (p 0))) * Complex.I =
      Complex.I * (minkowskiInner (a 0) (p 0) : ℂ) := by
    push_cast
    have h_cancel : (2 * Real.pi : ℂ) * (2 * Real.pi : ℂ)⁻¹ = 1 := by
      apply mul_inv_cancel₀
      exact_mod_cast hpi
    calc (2 * Real.pi : ℂ) * ((2 * Real.pi : ℂ)⁻¹ * (minkowskiInner (a 0) (p 0) : ℂ)) * Complex.I
      _ = ((2 * Real.pi : ℂ) * (2 * Real.pi : ℂ)⁻¹ *
              (minkowskiInner (a 0) (p 0) : ℂ)) * Complex.I := by ring
      _ = (1 * (minkowskiInner (a 0) (p 0) : ℂ)) * Complex.I := by rw [h_cancel]
      _ = Complex.I * (minkowskiInner (a 0) (p 0) : ℂ) := by ring
  rw [h_mul]

lemma vladimirov_kernel_zero_z (n : ℕ) (p : Fin n → Fin 4 → ℝ) :
    vladimirov_kernel n 0 p = 1 := by
  dsimp [vladimirov_kernel]
  have h_zero : (∑ k : Fin n, minkowskiInnerC (fun μ => (p k μ : ℂ)) 0) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    dsimp [minkowskiInnerC]
    ring
  rw [h_zero]
  ring_nf
  exact Complex.exp_zero

lemma test_phase_product_eq_one (x : ℂ) :
    Complex.exp x * Complex.exp (-x) = 1 := by
  rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]

lemma test_integrand_shift_eq (a : Fin 4 → ℝ) (x : Fin 1 → Fin 4 → ℝ)
    (v : EuclideanSpace ℝ (Fin 1 × Fin 4)) :
    Real.fourierChar (-inner ℝ v (piSpaceEquiv 1 (minkowskiFlipFun 1 x) -
        piSpaceEquiv 1 (minkowskiFlipFun 1 (posScaledMomentum (fun _ => a))))) •
      (vladimirov_psi 1 1 Real.zero_lt_one (fun _ μ => (a μ : ℂ)) ((piSpaceEquiv 1).symm v)) =
    Real.fourierChar (-inner ℝ v (piSpaceEquiv 1 (minkowskiFlipFun 1 x))) •
      (vladimirov_psi 1 1 Real.zero_lt_one 0 ((piSpaceEquiv 1).symm v)) := by
  let p := (piSpaceEquiv 1).symm v
  have hp_v : (piSpaceEquiv 1) p = v := (piSpaceEquiv 1).apply_symm_apply v
  let wx := piSpaceEquiv 1 (minkowskiFlipFun 1 x)
  let wa := piSpaceEquiv 1 (minkowskiFlipFun 1 (posScaledMomentum (fun _ => a)))
  have h_inner_sub : inner ℝ v (wx - wa) = inner ℝ v wx - inner ℝ v wa :=
    inner_sub_right _ _ _
  have h_neg_sub : - (inner ℝ v wx - inner ℝ v wa) = - inner ℝ v wx + inner ℝ v wa := by ring
  rw [Circle.smul_def, Circle.smul_def]
  have h_fc_add : (Real.fourierChar (-inner ℝ v wx + inner ℝ v wa) : ℂ) =
      (Real.fourierChar (-inner ℝ v wx) : ℂ) * (Real.fourierChar (inner ℝ v wa) : ℂ) := by
    rw [Real.fourierChar_apply, Real.fourierChar_apply, Real.fourierChar_apply]
    push_cast
    rw [← Complex.exp_add]
    congr 1
    ring
  change (Real.fourierChar (- (inner ℝ v (wx - wa))) : ℂ) * _ = _
  rw [h_inner_sub, h_neg_sub, h_fc_add]
  have h_v_flip : inner ℝ v wa =
      inner ℝ (piSpaceEquiv 1 (posScaledMomentum (fun _ => a)))
        (piSpaceEquiv 1 (minkowskiFlipFun 1 p)) := by
    rw [← hp_v, real_inner_comm]
    dsimp [wa]
    rw [inner_piSpaceEquiv_minkowskiFlip]
    rw [real_inner_comm, inner_piSpaceEquiv_minkowskiFlip]
    exact minkowskiInner_comm _ _
  have h_phase := test_phase_cancel_inv p (fun _ => a)
  dsimp [vladimirov_psi]
  have h_k0 : vladimirov_kernel 1 0 p = 1 := vladimirov_kernel_zero_z 1 p
  rw [h_k0, mul_one]
  have h_k_a : vladimirov_kernel 1 (fun _ μ => (a μ : ℂ)) p =
      Complex.exp (- Complex.I * (minkowskiInner (p 0) a : ℂ)) := by
    dsimp [vladimirov_kernel]
    have h_sum : (∑ k : Fin 1, minkowskiInnerC (fun μ => (p k μ : ℂ)) (fun μ => (a μ : ℂ))) =
        ((minkowskiInner (p 0) a : ℝ) : ℂ) := by
      rw [Fin.sum_univ_one]
      dsimp [minkowskiInnerC]
      rw [minkowskiInner_explicit]
      push_cast
      ring
    rw [h_sum]
  rw [h_k_a]
  have h_comm : minkowskiInner ((fun _ => a : Fin 1 → Fin 4 → ℝ) 0) (p 0) =
      minkowskiInner (p 0) a := by
    dsimp
    exact minkowskiInner_comm a (p 0)
  rw [h_v_flip, h_phase, h_comm]
  have h_exp_neg : - Complex.I * (minkowskiInner (p 0) a : ℂ) =
      - (Complex.I * (minkowskiInner (p 0) a : ℂ)) := by ring
  rw [h_exp_neg]
  have h_prod := test_phase_product_eq_one (Complex.I * (minkowskiInner (p 0) a : ℂ))
  calc (Real.fourierChar (-inner ℝ v wx) : ℂ) *
        Complex.exp (Complex.I * (minkowskiInner (p 0) a : ℂ)) *
        (((vladimirovCutoffBump 1 1 Real.zero_lt_one p : ℝ) : ℂ) *
          Complex.exp (- (Complex.I * (minkowskiInner (p 0) a : ℂ))))
    _ = (Real.fourierChar (-inner ℝ v wx) : ℂ) *
        (((vladimirovCutoffBump 1 1 Real.zero_lt_one p : ℝ) : ℂ) *
          (Complex.exp (Complex.I * (minkowskiInner (p 0) a : ℂ)) *
            Complex.exp (- (Complex.I * (minkowskiInner (p 0) a : ℂ))))) := by ring
    _ = (Real.fourierChar (-inner ℝ v wx) : ℂ) *
        (((vladimirovCutoffBump 1 1 Real.zero_lt_one p : ℝ) : ℂ) * 1) := by
      rw [h_prod]
    _ = (Real.fourierChar (-inner ℝ v wx) : ℂ) *
        ((vladimirovCutoffBump 1 1 Real.zero_lt_one p : ℝ) : ℂ) := by ring

lemma test_translation (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (hP : PoincareCovariant R W) (α : Fin 1 → ι) (a : Fin 4 → ℝ) :
    W 1 α (invMinkowskiFourierCLM 1
      (vladimirov_psi_schwartz 1 1 Real.zero_lt_one (fun _ μ => (a μ : ℂ)))) =
    W 1 α (invMinkowskiFourierCLM 1
      (vladimirov_psi_schwartz 1 1 Real.zero_lt_one 0)) := by
  let b : Fin 4 → ℝ := - (posScaledMomentum (fun _ => a)) 0
  let f := invMinkowskiFourierCLM 1 (vladimirov_psi_schwartz 1 1 Real.zero_lt_one 0)
  let f' := invMinkowskiFourierCLM 1
    (vladimirov_psi_schwartz 1 1 Real.zero_lt_one (fun _ μ => (a μ : ℂ)))
  have h_shift : ∀ x : Fin 1 → Fin 4 → ℝ, f' (fun i => x i + b) = f x := by
    intro x
    rw [invMinkowskiFourierCLM_apply_one, invMinkowskiFourierCLM_apply_one]
    have h_add : (fun i => x i + b) = x + (fun _ => b) := by
      ext i μ
      rfl
    rw [h_add]
    have h_flip : minkowskiFlipFun 1 (x + (fun _ => b)) =
        minkowskiFlipFun 1 x + minkowskiFlipFun 1 (fun _ => b) :=
      map_add (minkowskiFlipEquiv 1) x (fun _ => b)
    rw [h_flip]
    have h_b_eq : (fun _ : Fin 1 => b) = - posScaledMomentum (fun _ => a) := by
      ext i
      fin_cases i
      rfl
    have h_b_flip : minkowskiFlipFun 1 (fun _ => b) =
        - minkowskiFlipFun 1 (posScaledMomentum (fun _ => a)) := by
      rw [h_b_eq]
      exact map_neg (minkowskiFlipEquiv 1) _
    have h_pi : piSpaceEquiv 1 (minkowskiFlipFun 1 x + minkowskiFlipFun 1 (fun _ => b)) =
        piSpaceEquiv 1 (minkowskiFlipFun 1 x) +
        piSpaceEquiv 1 (minkowskiFlipFun 1 (fun _ => b)) :=
      map_add (piSpaceEquiv 1) _ _
    rw [h_pi, h_b_flip]
    have h_b_pi : piSpaceEquiv 1 (- minkowskiFlipFun 1 (posScaledMomentum (fun _ => a))) =
        - piSpaceEquiv 1 (minkowskiFlipFun 1 (posScaledMomentum (fun _ => a))) :=
      map_neg (piSpaceEquiv 1) _
    rw [h_b_pi, ← sub_eq_add_neg]
    rw [Real.fourier_eq, Real.fourier_eq]
    congr 1
    ext v
    dsimp [Function.comp, vladimirov_psi_schwartz, HasCompactSupport.toSchwartzMap]
    exact test_integrand_shift_eq a x v
  exact translationInvariant_of_poincare R W hP 1 b α f f' h_shift

lemma vladimirov_H_real_eq_const (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (hP : PoincareCovariant R W) (α : Fin 1 → ι) (x : Fin 1 → Fin 4 → ℝ) :
    vladimirov_H W 1 α (fun i k => (x i k : ℂ)) = vladimirov_H W 1 α 0 := by
  have h_x0 : (fun i k => (x i k : ℂ)) = fun _ μ => ((x 0 μ : ℝ) : ℂ) := by
    ext i μ
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    rfl
  rw [h_x0]
  dsimp [vladimirov_H, vladimirov_H_cutoff]
  exact test_translation R W hP α (x 0)

lemma vladimirov_H_boundary_integrand_eq (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (hP : PoincareCovariant R W) (α : Fin 1 → ι) (f : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ)
    (v : Fin 4 → ℝ) (t : ℝ) :
    (∫ x : Fin 1 → Fin 4 → ℝ,
        vladimirov_H W 1 α
          (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ)) * f x) =
    vladimirov_H W 1 α 0 * ∫ x, f x := by
  have h_shift : (fun x : Fin 1 → Fin 4 → ℝ =>
      vladimirov_H W 1 α
        (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ)) * f x) =
      (fun x => vladimirov_H W 1 α 0 * f x) := by
    ext x
    have h_s := shift_zero_of_fin_one t v x
    rw [h_s]
    have h_c := vladimirov_H_real_eq_const R W hP α x
    rw [h_c]
  rw [h_shift]
  exact integral_const_mul (vladimirov_H W 1 α 0) (fun x => f x)

lemma vladimirov_H_boundary_tendsto (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (hP : PoincareCovariant R W) (α : Fin 1 → ι) (f : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ)
    (v : Fin 4 → ℝ) :
    Tendsto (fun t : ℝ => ∫ x : Fin 1 → Fin 4 → ℝ,
        vladimirov_H W 1 α
          (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ)) * f x)
      (𝓝[>] 0)
      (𝓝 (vladimirov_H W 1 α 0 * ∫ x, f x)) := by
  have h_eq : (fun t : ℝ => ∫ x : Fin 1 → Fin 4 → ℝ,
      vladimirov_H W 1 α
        (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ)) * f x) =
      (fun _ => vladimirov_H W 1 α 0 * ∫ x, f x) := by
    ext t
    exact vladimirov_H_boundary_integrand_eq R W hP α f v t
  rw [h_eq]
  exact tendsto_const_nhds

lemma vladimirov_kernel_zero_p (z : Fin 1 → Fin 4 → ℂ) :
    vladimirov_kernel 1 z 0 = 1 := by
  dsimp [vladimirov_kernel]
  have h_zero : (∑ k : Fin 1, minkowskiInnerC (fun _ => 0) (z k)) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    dsimp [minkowskiInnerC]
    ring
  rw [h_zero]
  ring_nf
  exact Complex.exp_zero

lemma vladimirov_psi_zero_p (z : Fin 1 → Fin 4 → ℂ) :
    vladimirov_psi 1 1 Real.zero_lt_one z 0 = 1 := by
  dsimp [vladimirov_psi]
  have h_bump : (vladimirovCutoffBump 1 1 Real.zero_lt_one 0 : ℝ) = 1 := by
    apply (vladimirovCutoffBump 1 1 Real.zero_lt_one).one_of_mem_closedBall
    simp only [Metric.mem_closedBall, dist_self]
    exact zero_le_one
  rw [h_bump, vladimirov_kernel_zero_p]
  push_cast
  ring

lemma vladimirov_fourier_eval_zero (z : Fin 1 → Fin 4 → ℂ) :
    minkowskiFourier (invMinkowskiFourierCLM 1
      (vladimirov_psi_schwartz 1 1 Real.zero_lt_one z)) 0 = 1 := by
  rw [minkowskiFourier_invMinkowskiFourierCLM_one]
  have h_sm : scaledMomentum (0 : Fin 1 → Fin 4 → ℝ) = 0 := by
    ext i μ
    simp [scaledMomentum]
  rw [h_sm]
  change vladimirov_psi 1 1 Real.zero_lt_one z 0 = 1
  exact vladimirov_psi_zero_p z

lemma vladimirov_fourier_diff_zero (z w : Fin 1 → Fin 4 → ℂ) :
    minkowskiFourier
      (invMinkowskiFourierCLM 1 (vladimirov_psi_schwartz 1 1 Real.zero_lt_one z) -
       invMinkowskiFourierCLM 1 (vladimirov_psi_schwartz 1 1 Real.zero_lt_one w)) 0 = 0 := by
  rw [minkowskiFourier_sub]
  rw [vladimirov_fourier_eval_zero, vladimirov_fourier_eval_zero, sub_self]

lemma minkowskiFourier_eval_zero (f : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) :
    minkowskiFourier f 0 = ∫ x, f x := by
  dsimp [minkowskiFourier]
  have h_exp : (fun x : Fin 1 → Fin 4 → ℝ =>
      f x * Complex.exp (-(Complex.I *
        ((∑ k : Fin 1, minkowskiInner (0 : Fin 4 → ℝ) (x k) : ℝ) : ℂ)))) =
      (fun x => f x) := by
    ext x
    have h_inner : (∑ k : Fin 1, minkowskiInner (0 : Fin 4 → ℝ) (x k)) = 0 := by
      rw [Fin.sum_univ_one]
      simp [minkowskiInner_explicit]
    rw [h_inner]
    push_cast
    ring_nf
    rw [Complex.exp_zero, mul_one]
  rw [h_exp]

lemma vladimirov_H_analytic_at_one
    (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (_hP : PoincareCovariant R W) (α : Fin 1 → ι)
    (z : Fin 1 → Fin 4 → ℂ) (_hz : z ∈ forward_tube_n 1)
    (h_one : ∀ f : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ,
      W 1 α f = vladimirov_H W 1 α 0 * ∫ x, f x) :
    AnalyticAt ℂ (vladimirov_H W 1 α) z := by
  have h_const : ∀ w : Fin 1 → Fin 4 → ℂ, vladimirov_H W 1 α w = vladimirov_H W 1 α 0 := by
    intro w
    let f_w := invMinkowskiFourierCLM 1 (vladimirov_psi_schwartz 1 1 Real.zero_lt_one w)
    let f_0 := invMinkowskiFourierCLM 1 (vladimirov_psi_schwartz 1 1 Real.zero_lt_one 0)
    change W 1 α f_w = W 1 α f_0
    have h_sub : W 1 α f_w - W 1 α f_0 = W 1 α (f_w - f_0) := (map_sub (W 1 α) f_w f_0).symm
    rw [← sub_eq_zero, h_sub]
    rw [h_one (f_w - f_0)]
    have h_int_zero : (∫ x, (f_w - f_0) x) = 0 := by
      rw [← minkowskiFourier_eval_zero]
      exact vladimirov_fourier_diff_zero w 0
    rw [h_int_zero, mul_zero]
  have h_fun_eq : (vladimirov_H W 1 α) = fun _ => vladimirov_H W 1 α 0 := by
    ext w
    exact h_const w
  rw [h_fun_eq]
  exact analyticAt_const

lemma vladimirov_H_boundary_one
    (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (hP : PoincareCovariant R W) (α : Fin 1 → ι)
    (f : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) (v : Fin 4 → ℝ) (_hv : v ∈ forward_light_cone)
    (h_one : W 1 α f = vladimirov_H W 1 α 0 * ∫ x, f x) :
    Tendsto (fun t : ℝ => ∫ x : Fin 1 → Fin 4 → ℝ,
        vladimirov_H W 1 α
          (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ)) * f x)
      (𝓝[>] 0) (𝓝 (W 1 α f)) := by
  rw [h_one]
  exact vladimirov_H_boundary_tendsto R W hP α f v

omit [Fintype ι] [DecidableEq ι] in
lemma W_one_vanish_of_fourier_zero (W : WightmanFamily ι)
    (hspec : SpectrumCondition W) (α : Fin 1 → ι)
    (f : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ)
    (hf : ∀ p ∈ Metric.ball (0 : Fin 1 → Fin 4 → ℝ) 1, minkowskiFourier f p = 0) :
    W 1 α f = 0 := by
  apply hspec 1 α f
  refine Or.inl ⟨Metric.ball 0 1, Metric.isOpen_ball, ?_, hf⟩
  intro p hp
  have hp0 : p = 0 := spectralRegion_one_eq_zero p hp
  subst hp0
  exact Metric.mem_ball_self Real.zero_lt_one

omit [Fintype ι] [DecidableEq ι] in
lemma W_one_eq_of_fourier_eq (W : WightmanFamily ι)
    (hspec : SpectrumCondition W) (α : Fin 1 → ι)
    (f g : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ)
    (hfg : ∀ p ∈ Metric.ball (0 : Fin 1 → Fin 4 → ℝ) 1,
      minkowskiFourier f p = minkowskiFourier g p) :
    W 1 α f = W 1 α g := by
  have h_sub : W 1 α f - W 1 α g = W 1 α (f - g) := (map_sub (W 1 α) f g).symm
  rw [← sub_eq_zero, h_sub]
  apply W_one_vanish_of_fourier_zero W hspec α (f - g)
  intro p hp
  rw [minkowskiFourier_sub]
  rw [hfg p hp, sub_self]

lemma W_one_eq_integral_of_zero_integral (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (_hspec : SpectrumCondition W) (_hP : PoincareCovariant R W) (α : Fin 1 → ι)
    (h_zero : ∀ g : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ, (∫ x, g x) = 0 → W 1 α g = 0)
    (f : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) :
    W 1 α f = vladimirov_H W 1 α 0 * ∫ x, f x := by
  let g0 := invMinkowskiFourierCLM 1 (vladimirov_psi_schwartz 1 1 Real.zero_lt_one 0)
  have h_int_g0 : (∫ x, g0 x) = 1 := by
    rw [← minkowskiFourier_eval_zero]
    exact vladimirov_fourier_eval_zero 0
  let c := ∫ x, f x
  let g := f - c • g0
  have h_int_g : (∫ x, g x) = 0 := by
    change (∫ x, (f - c • g0) x) = 0
    have h_sub : (∫ x, (f - c • g0) x) = (∫ x, f x) - (∫ x, (c • g0) x) := by
      exact integral_sub f.integrable (g0.integrable.smul c)
    have h_smul : (∫ x, (c • g0) x) = c • (∫ x, g0 x) := integral_smul c g0
    rw [h_sub, h_smul, h_int_g0, smul_eq_mul, mul_one, sub_self]
  have h_Wg : W 1 α g = 0 := h_zero g h_int_g
  dsimp [g] at h_Wg
  rw [map_sub, map_smul] at h_Wg
  change W 1 α f - c • W 1 α g0 = 0 at h_Wg
  rw [sub_eq_zero] at h_Wg
  rw [h_Wg]
  dsimp [c, g0, vladimirov_H, vladimirov_H_cutoff]
  exact mul_comm _ _

lemma W_one_vanish_of_psi_sum_zero (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (hP : PoincareCovariant R W) (α : Fin 1 → ι)
    {m : ℕ} (c : Fin m → ℂ) (a : Fin m → Fin 4 → ℝ)
    (hc : ∑ j, c j = 0) :
    W 1 α (∑ j, c j • invMinkowskiFourierCLM 1
      (vladimirov_psi_schwartz 1 1 Real.zero_lt_one (fun _ μ => (a j μ : ℂ)))) = 0 := by
  have h_lin : W 1 α (∑ j, c j • invMinkowskiFourierCLM 1
      (vladimirov_psi_schwartz 1 1 Real.zero_lt_one (fun _ μ => (a j μ : ℂ)))) =
      ∑ j, c j * W 1 α (invMinkowskiFourierCLM 1
        (vladimirov_psi_schwartz 1 1 Real.zero_lt_one (fun _ μ => (a j μ : ℂ)))) := by
    simp_rw [map_sum, map_smul, smul_eq_mul]
  rw [h_lin]
  have h_trans : ∀ j, W 1 α (invMinkowskiFourierCLM 1
      (vladimirov_psi_schwartz 1 1 Real.zero_lt_one (fun _ μ => (a j μ : ℂ)))) =
      vladimirov_H W 1 α 0 := by
    intro j
    exact test_translation R W hP α (a j)
  simp_rw [h_trans, ← Finset.sum_mul, hc, zero_mul]

lemma W_one_sub_shift_zero (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (hP : PoincareCovariant R W) (α : Fin 1 → ι)
    (h : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) (a : Fin 4 → ℝ)
    (h' : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ)
    (h_shift : ∀ x, h' (fun i => x i + a) = h x) :
    W 1 α (h' - h) = 0 := by
  rw [map_sub]
  have h_eq : W 1 α h' = W 1 α h :=
    translationInvariant_of_poincare R W hP 1 a α h h' h_shift
  rw [h_eq, sub_self]

lemma W_one_vanish_of_fourier_sub_shift (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (hspec : SpectrumCondition W) (hP : PoincareCovariant R W) (α : Fin 1 → ι)
    (g : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ)
    (h : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) (a : Fin 4 → ℝ)
    (h' : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ)
    (h_shift : ∀ x, h' (fun i => x i + a) = h x)
    (hfg : ∀ p ∈ Metric.ball (0 : Fin 1 → Fin 4 → ℝ) 1,
      minkowskiFourier g p = minkowskiFourier (h' - h) p) :
    W 1 α g = 0 := by
  have h_eq : W 1 α g = W 1 α (h' - h) := W_one_eq_of_fourier_eq W hspec α g (h' - h) hfg
  rw [h_eq]
  exact W_one_sub_shift_zero R W hP α h a h' h_shift

lemma W_one_sum_shift_zero (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (hP : PoincareCovariant R W) (α : Fin 1 → ι) {m : ℕ}
    (h : Fin m → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) (a : Fin m → Fin 4 → ℝ)
    (h' : Fin m → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ)
    (h_shift : ∀ j x, h' j (fun i => x i + a j) = h j x) :
    W 1 α (∑ j, (h' j - h j)) = 0 := by
  rw [map_sum]
  have h_each : ∀ j, W 1 α (h' j - h j) = 0 := by
    intro j
    exact W_one_sub_shift_zero R W hP α (h j) (a j) (h' j) (h_shift j)
  simp_rw [h_each, Finset.sum_const_zero]

lemma W_one_vanish_of_fourier_sum_shift (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (hspec : SpectrumCondition W) (hP : PoincareCovariant R W) (α : Fin 1 → ι)
    (g : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) {m : ℕ}
    (h : Fin m → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) (a : Fin m → Fin 4 → ℝ)
    (h' : Fin m → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ)
    (h_shift : ∀ j x, h' j (fun i => x i + a j) = h j x)
    (hfg : ∀ p ∈ Metric.ball (0 : Fin 1 → Fin 4 → ℝ) 1,
      minkowskiFourier g p = minkowskiFourier (∑ j, (h' j - h j)) p) :
    W 1 α g = 0 := by
  have h_eq : W 1 α g = W 1 α (∑ j, (h' j - h j)) :=
    W_one_eq_of_fourier_eq W hspec α g (∑ j, (h' j - h j)) hfg
  rw [h_eq]
  exact W_one_sum_shift_zero R W hP α h a h' h_shift

omit [Fintype ι] [DecidableEq ι] in
lemma exists_shift_fourier_exp_sub_one (a : Fin 4 → ℝ) :
    ∃ (h h' : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) (b : Fin 4 → ℝ),
      (∀ x, h' (fun i => x i + b) = h x) ∧
      (∀ p ∈ Metric.ball (0 : Fin 1 → Fin 4 → ℝ) 1,
        minkowskiFourier (h' - h) p =
          Complex.exp (-(Complex.I * ((minkowskiInner (p 0) a : ℝ) : ℂ))) - 1) := by
  let a' : Fin 4 → ℝ := - (2 * Real.pi) • a
  let b : Fin 4 → ℝ := - (posScaledMomentum (fun _ => a')) 0
  let h := invMinkowskiFourierCLM 1 (vladimirov_psi_schwartz 1 1 Real.zero_lt_one 0)
  let h' := invMinkowskiFourierCLM 1
    (vladimirov_psi_schwartz 1 1 Real.zero_lt_one (fun _ μ => (a' μ : ℂ)))
  refine ⟨h, h', b, ?_, ?_⟩
  · intro x
    rw [invMinkowskiFourierCLM_apply_one, invMinkowskiFourierCLM_apply_one]
    have h_add : (fun i => x i + b) = x + (fun _ => b) := by ext i μ; rfl
    rw [h_add]
    have h_flip : minkowskiFlipFun 1 (x + (fun _ => b)) =
        minkowskiFlipFun 1 x + minkowskiFlipFun 1 (fun _ => b) :=
      map_add (minkowskiFlipEquiv 1) x (fun _ => b)
    rw [h_flip]
    have h_b_eq : (fun _ : Fin 1 => b) = - posScaledMomentum (fun _ => a') := by
      ext i; fin_cases i; rfl
    have h_b_flip : minkowskiFlipFun 1 (fun _ => b) =
        - minkowskiFlipFun 1 (posScaledMomentum (fun _ => a')) := by
      rw [h_b_eq]; exact map_neg (minkowskiFlipEquiv 1) _
    have h_pi : piSpaceEquiv 1 (minkowskiFlipFun 1 x + minkowskiFlipFun 1 (fun _ => b)) =
        piSpaceEquiv 1 (minkowskiFlipFun 1 x) +
        piSpaceEquiv 1 (minkowskiFlipFun 1 (fun _ => b)) :=
      map_add (piSpaceEquiv 1) _ _
    rw [h_pi, h_b_flip]
    have h_b_pi : piSpaceEquiv 1 (- minkowskiFlipFun 1 (posScaledMomentum (fun _ => a'))) =
        - piSpaceEquiv 1 (minkowskiFlipFun 1 (posScaledMomentum (fun _ => a'))) :=
      map_neg (piSpaceEquiv 1) _
    rw [h_b_pi, ← sub_eq_add_neg]
    rw [Real.fourier_eq, Real.fourier_eq]
    congr 1
    ext v
    dsimp [Function.comp, vladimirov_psi_schwartz, HasCompactSupport.toSchwartzMap]
    exact test_integrand_shift_eq a' x v
  · intro p hp
    rw [minkowskiFourier_sub]
    dsimp [h, h']
    rw [minkowskiFourier_invMinkowskiFourierCLM_one, minkowskiFourier_invMinkowskiFourierCLM_one]
    have hp_norm : ‖p‖ < 1 := by
      rw [Metric.mem_ball, dist_zero_right] at hp
      exact hp
    have h_sc_norm := scaledMomentum_lt_one p hp_norm
    change vladimirov_psi 1 1 Real.zero_lt_one (fun _ μ => (a' μ : ℂ)) (scaledMomentum p) -
        vladimirov_psi 1 1 Real.zero_lt_one 0 (scaledMomentum p) =
      Complex.exp (-(Complex.I * ((minkowskiInner (p 0) a : ℝ) : ℂ))) - 1
    dsimp [vladimirov_psi]
    have h_bump : (vladimirovCutoffBump 1 1 Real.zero_lt_one (scaledMomentum p) : ℝ) = 1 := by
      apply (vladimirovCutoffBump 1 1 Real.zero_lt_one).one_of_mem_closedBall
      simp only [Metric.mem_closedBall, dist_zero_right]
      exact h_sc_norm.le
    rw [h_bump, Complex.ofReal_one, one_mul, one_mul]
    have h_zero : vladimirov_kernel 1 0 (scaledMomentum p) = 1 := by
      dsimp [vladimirov_kernel]
      have h_inn0 : (∑ k : Fin 1, minkowskiInnerC (fun μ => ((scaledMomentum p k μ : ℝ) : ℂ))
          (0 : Fin 4 → ℂ)) = 0 := by
        rw [Fin.sum_univ_one]
        dsimp [minkowskiInnerC]
        ring
      rw [h_inn0]
      ring_nf
      exact Complex.exp_zero
    rw [h_zero]
    dsimp [vladimirov_kernel]
    have h_sum1 : (∑ k : Fin 1, minkowskiInnerC (fun μ => ((scaledMomentum p k μ : ℝ) : ℂ))
        (fun μ => ((a' μ : ℝ) : ℂ))) =
        ((minkowskiInner (p 0) a : ℝ) : ℂ) := by
      rw [Fin.sum_univ_one]
      have hpi : (2 * Real.pi : ℂ) ≠ 0 := by
        exact_mod_cast mul_ne_zero two_ne_zero (ne_of_gt Real.pi_pos)
      have h_cancel : (- (2 * (Real.pi : ℂ))⁻¹) * (- (2 * (Real.pi : ℂ))) = 1 := by
        rw [neg_mul_neg, inv_mul_cancel₀ hpi]
      dsimp [scaledMomentum, a', minkowskiInnerC]
      rw [minkowskiInner_explicit (p 0) a]
      push_cast
      linear_combination
        (p 0 0 * a 0 - p 0 1 * a 1 - p 0 2 * a 2 - p 0 3 * a 3) * h_cancel
    rw [h_sum1]
    congr 2
    ring

omit [Fintype ι] [DecidableEq ι] in
lemma taylor_ftc (f : (Fin 1 → Fin 4 → ℝ) → ℂ) (p : Fin 1 → Fin 4 → ℝ)
    (hf : ∀ t ∈ Set.Icc (0 : ℝ) 1, ContDiffAt ℝ 1 f (t • p)) :
    f p = f 0 + ∫ t in 0..1, fderiv ℝ f (t • p) p := by
  have h := map_add_eq_sum_add_integral_iteratedFDeriv (n := 0) (x := 0) (y := p) (hf := by
    intro t ht
    simpa using hf t ht)
  simp only [zero_add, Finset.range_one, Finset.sum_singleton, Nat.factorial_zero, Nat.cast_one,
    inv_one, iteratedFDeriv_zero_apply, one_smul, pow_zero] at h
  have h_one : ∀ t : ℝ, iteratedFDeriv ℝ 1 f (t • p) (fun _ => p) = fderiv ℝ f (t • p) p := by
    intro t
    exact iteratedFDeriv_one_apply (fun _ => p)
  simp_rw [h_one] at h
  exact h

def stdBasis (k : Fin 4) : Fin 1 → Fin 4 → ℝ :=
  fun _ μ => if μ = k then 1 else 0

omit [Fintype ι] [DecidableEq ι] in
lemma p_eq_sum_stdBasis (p : Fin 1 → Fin 4 → ℝ) :
    p = ∑ k : Fin 4, (p 0 k) • stdBasis k := by
  ext i μ
  have hi : i = 0 := Subsingleton.elim i 0
  subst hi
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, stdBasis]
  rw [Finset.sum_eq_single μ]
  · simp
  · intro b _ hb
    simp [hb.symm]
  · intro h
    exact (h (Finset.mem_univ μ)).elim

omit [Fintype ι] [DecidableEq ι] in
lemma fderiv_apply_eq_sum (L : (Fin 1 → Fin 4 → ℝ) →L[ℝ] ℂ) (p : Fin 1 → Fin 4 → ℝ) :
    L p = ∑ k : Fin 4, (p 0 k : ℂ) * L (stdBasis k) := by
  conv_lhs => rw [p_eq_sum_stdBasis p]
  rw [map_sum]
  congr 1
  ext k
  rw [map_smul, Complex.real_smul]

noncomputable def hadamardTerm (f : (Fin 1 → Fin 4 → ℝ) → ℂ) (k : Fin 4)
    (p : Fin 1 → Fin 4 → ℝ) : ℂ :=
  ∫ t in 0..1, fderiv ℝ f (t • p) (stdBasis k)

omit [Fintype ι] [DecidableEq ι] in
theorem hadamard_identity (f : (Fin 1 → Fin 4 → ℝ) → ℂ) (p : Fin 1 → Fin 4 → ℝ)
    (hf : ∀ t ∈ Set.Icc (0 : ℝ) 1, ContDiffAt ℝ 1 f (t • p)) (hf0 : f 0 = 0)
    (hint : ∀ k : Fin 4, IntervalIntegrable (fun t : ℝ => fderiv ℝ f (t • p) (stdBasis k))
      MeasureTheory.volume 0 1) :
    f p = ∑ k : Fin 4, (p 0 k : ℂ) * hadamardTerm f k p := by
  have h_ftc := taylor_ftc f p hf
  rw [hf0, zero_add] at h_ftc
  rw [h_ftc]
  have h_sum : (fun t : ℝ => fderiv ℝ f (t • p) p) =
      fun t => ∑ k : Fin 4, (p 0 k : ℂ) * fderiv ℝ f (t • p) (stdBasis k) := by
    ext t
    exact fderiv_apply_eq_sum (fderiv ℝ f (t • p)) p
  rw [h_sum]
  rw [intervalIntegral.integral_finsetSum (fun k _ => (hint k).const_mul (p 0 k : ℂ))]
  congr 1
  ext k
  dsimp [hadamardTerm]
  exact intervalIntegral.integral_const_mul (p 0 k : ℂ) (fun t => fderiv ℝ f (t • p) (stdBasis k))

noncomputable def evalAtBasis (k : Fin 4) :
    ((Fin 1 → Fin 4 → ℝ) →L[ℝ] ℂ) →L[ℝ] ℂ :=
  ContinuousLinearMap.apply ℝ ℂ (stdBasis k)

lemma evalAtBasis_apply (k : Fin 4) (L : (Fin 1 → Fin 4 → ℝ) →L[ℝ] ℂ) :
    evalAtBasis k L = L (stdBasis k) := rfl

omit [Fintype ι] [DecidableEq ι] in
lemma contDiff_fderiv_apply_top (f : (Fin 1 → Fin 4 → ℝ) → ℂ)
    (hf : ContDiff ℝ ⊤ f) (k : Fin 4) :
    ContDiff ℝ ⊤ (fun q => fderiv ℝ f q (stdBasis k)) := by
  have h_comp : (fun q => fderiv ℝ f q (stdBasis k)) = (evalAtBasis k) ∘ (fderiv ℝ f) := rfl
  rw [h_comp]
  apply (evalAtBasis k).contDiff.comp
  exact hf.fderiv_right le_top

omit [Fintype ι] [DecidableEq ι] in
lemma contDiff_fderiv_scaled_apply_top (f : (Fin 1 → Fin 4 → ℝ) → ℂ)
    (hf : ContDiff ℝ ⊤ f) (k : Fin 4) (t : ℝ) :
    ContDiff ℝ ⊤ (fun p => fderiv ℝ f (t • p) (stdBasis k)) := by
  have h_scale : ContDiff ℝ ⊤ (fun p : Fin 1 → Fin 4 → ℝ => t • p) :=
    (t • ContinuousLinearMap.id ℝ (Fin 1 → Fin 4 → ℝ)).contDiff
  exact (contDiff_fderiv_apply_top f hf k).comp h_scale

noncomputable def hadamardIntegrandFDeriv (f : (Fin 1 → Fin 4 → ℝ) → ℂ) (k : Fin 4)
    (t : ℝ) (p : Fin 1 → Fin 4 → ℝ) : (Fin 1 → Fin 4 → ℝ) →L[ℝ] ℂ :=
  t • (fderiv ℝ (fun q => fderiv ℝ f q (stdBasis k)) (t • p))

omit [Fintype ι] [DecidableEq ι] in
lemma hasFDerivAt_hadamardIntegrand (f : (Fin 1 → Fin 4 → ℝ) → ℂ)
    (hf : ContDiff ℝ 2 f) (k : Fin 4) (t : ℝ) (p : Fin 1 → Fin 4 → ℝ) :
    HasFDerivAt (fun q => fderiv ℝ f (t • q) (stdBasis k))
      (hadamardIntegrandFDeriv f k t p) p := by
  let g := fun q => fderiv ℝ f q (stdBasis k)
  have hg_diff : DifferentiableAt ℝ g (t • p) := by
    have hg_c1 : ContDiff ℝ 1 g := by
      have h_comp : g = (evalAtBasis k) ∘ (fderiv ℝ f) := rfl
      rw [h_comp]
      apply (evalAtBasis k).contDiff.comp
      exact hf.fderiv_right le_rfl
    exact hg_c1.differentiable one_ne_zero (t • p)
  let L_t : (Fin 1 → Fin 4 → ℝ) →L[ℝ] (Fin 1 → Fin 4 → ℝ) :=
    t • ContinuousLinearMap.id ℝ (Fin 1 → Fin 4 → ℝ)
  have h_comp : (fun q => fderiv ℝ f (t • q) (stdBasis k)) = g ∘ L_t := rfl
  rw [h_comp]
  have h_chain := HasFDerivAt.comp p hg_diff.hasFDerivAt L_t.hasFDerivAt
  dsimp [hadamardIntegrandFDeriv, g]
  have h_eq : (fderiv ℝ (fun q => fderiv ℝ f q (stdBasis k)) (t • p)).comp L_t =
      t • (fderiv ℝ (fun q => fderiv ℝ f q (stdBasis k)) (t • p)) := by
    ext v
    simp [L_t]
  rw [h_eq] at h_chain
  exact h_chain

omit [Fintype ι] [DecidableEq ι] in
lemma continuous_hadamardIntegrandFDeriv (f : (Fin 1 → Fin 4 → ℝ) → ℂ)
    (hf : ContDiff ℝ ⊤ f) (k : Fin 4) :
    Continuous (fun (pt : (Fin 1 → Fin 4 → ℝ) × ℝ) =>
      hadamardIntegrandFDeriv f k pt.2 pt.1) := by
  let g := fun q => fderiv ℝ f q (stdBasis k)
  have hg_c2 : ContDiff ℝ 2 g := by
    have h_comp : g = (evalAtBasis k) ∘ (fderiv ℝ f) := rfl
    rw [h_comp]
    apply (evalAtBasis k).contDiff.comp
    exact hf.fderiv_right le_top
  have h_cont_dg : Continuous (fderiv ℝ g) := hg_c2.continuous_fderiv two_ne_zero
  have h_smul : Continuous (fun (pt : (Fin 1 → Fin 4 → ℝ) × ℝ) => pt.2 • pt.1) :=
    continuous_snd.smul continuous_fst
  have h_comp_cont : Continuous (fun (pt : (Fin 1 → Fin 4 → ℝ) × ℝ) =>
      fderiv ℝ g (pt.2 • pt.1)) :=
    h_cont_dg.comp h_smul
  exact continuous_snd.smul h_comp_cont

omit [Fintype ι] [DecidableEq ι] in
lemma continuous_hadamardIntegrand (f : (Fin 1 → Fin 4 → ℝ) → ℂ)
    (hf : ContDiff ℝ ⊤ f) (k : Fin 4) (x : Fin 1 → Fin 4 → ℝ) :
    Continuous (fun t : ℝ => fderiv ℝ f (t • x) (stdBasis k)) := by
  let g := fun q => fderiv ℝ f q (stdBasis k)
  have hg_cont : Continuous g := (contDiff_fderiv_apply_top f hf k).continuous
  exact hg_cont.comp (continuous_id.smul continuous_const)

omit [Fintype ι] [DecidableEq ι] in
lemma hasFDerivAt_hadamardTerm (f : (Fin 1 → Fin 4 → ℝ) → ℂ)
    (hf : ContDiff ℝ ⊤ f) (k : Fin 4) (p : Fin 1 → Fin 4 → ℝ) :
    HasFDerivAt (hadamardTerm f k)
      (∫ t in (0:ℝ)..1, hadamardIntegrandFDeriv f k t p) p := by
  have hs : Metric.ball p 1 ∈ 𝓝 p := Metric.ball_mem_nhds p zero_lt_one
  have hF_meas : ∀ᶠ (x : Fin 1 → Fin 4 → ℝ) in 𝓝 p,
      AEStronglyMeasurable (fun t : ℝ => fderiv ℝ f (t • x) (stdBasis k))
        (volume.restrict (Ι (0:ℝ) 1)) := by
    refine Filter.Eventually.of_forall (fun x => ?_)
    exact (continuous_hadamardIntegrand f hf k x).aestronglyMeasurable
  have hF_int : IntervalIntegrable (fun t : ℝ => fderiv ℝ f (t • p) (stdBasis k))
      volume 0 1 :=
    (continuous_hadamardIntegrand f hf k p).intervalIntegrable 0 1
  have hF'_meas : AEStronglyMeasurable (hadamardIntegrandFDeriv f k · p)
      (volume.restrict (Ι (0:ℝ) 1)) := by
    have h_pair : Continuous (fun t : ℝ => (p, t)) := by fun_prop
    have h_cont : Continuous (fun t : ℝ => hadamardIntegrandFDeriv f k t p) :=
      (continuous_hadamardIntegrandFDeriv f hf k).comp h_pair
    exact h_cont.aestronglyMeasurable
  let K : Set ((Fin 1 → Fin 4 → ℝ) × ℝ) :=
    (Metric.closedBall p 1) ×ˢ (Set.uIcc (0:ℝ) 1)
  have hK_comp : IsCompact K := (isCompact_closedBall p 1).prod isCompact_uIcc
  have h_cont_on : ContinuousOn (fun pt : (Fin 1 → Fin 4 → ℝ) × ℝ =>
      hadamardIntegrandFDeriv f k pt.2 pt.1) K :=
    (continuous_hadamardIntegrandFDeriv f hf k).continuousOn
  obtain ⟨C, hC⟩ := hK_comp.exists_bound_of_continuousOn h_cont_on
  have h_bound : ∀ᵐ (t : ℝ) ∂volume.restrict (Ι (0:ℝ) 1),
      ∀ x ∈ Metric.ball p 1, ‖hadamardIntegrandFDeriv f k t x‖ ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht x hx
    have hx_cl : x ∈ Metric.closedBall p 1 := Metric.ball_subset_closedBall hx
    have ht_icc : t ∈ Set.uIcc (0:ℝ) 1 := Set.uIoc_subset_uIcc ht
    exact hC (x, t) ⟨hx_cl, ht_icc⟩
  have bound_int : IntervalIntegrable (fun _ : ℝ => C) volume 0 1 :=
    intervalIntegrable_const
  have h_diff : ∀ᵐ (t : ℝ) ∂volume.restrict (Ι (0:ℝ) 1),
      ∀ x ∈ Metric.ball p 1,
        HasFDerivAt (fun q => fderiv ℝ f (t • q) (stdBasis k))
          (hadamardIntegrandFDeriv f k t x) x := by
    refine Filter.Eventually.of_forall (fun t => fun x _hx => ?_)
    exact hasFDerivAt_hadamardIntegrand f (hf.of_le le_top) k t x
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le'' hs hF_meas hF_int hF'_meas
    h_bound bound_int h_diff

omit [Fintype ι] [DecidableEq ι] in
lemma fderiv_hadamardTerm (f : (Fin 1 → Fin 4 → ℝ) → ℂ)
    (hf : ContDiff ℝ ⊤ f) (k : Fin 4) (p : Fin 1 → Fin 4 → ℝ) :
    fderiv ℝ (hadamardTerm f k) p = ∫ t in (0:ℝ)..1, hadamardIntegrandFDeriv f k t p :=
  (hasFDerivAt_hadamardTerm f hf k p).fderiv

omit [Fintype ι] [DecidableEq ι] in
lemma differentiable_hadamardTerm (f : (Fin 1 → Fin 4 → ℝ) → ℂ)
    (hf : ContDiff ℝ ⊤ f) (k : Fin 4) :
    Differentiable ℝ (hadamardTerm f k) := fun p =>
  (hasFDerivAt_hadamardTerm f hf k p).differentiableAt

omit [Fintype ι] [DecidableEq ι] in
lemma continuous_fderiv_hadamardTerm (f : (Fin 1 → Fin 4 → ℝ) → ℂ)
    (hf : ContDiff ℝ ⊤ f) (k : Fin 4) :
    Continuous (fderiv ℝ (hadamardTerm f k)) := by
  have h_eq : (fderiv ℝ (hadamardTerm f k)) =
      fun p => ∫ t in (0:ℝ)..1, hadamardIntegrandFDeriv f k t p := by
    funext p
    exact fderiv_hadamardTerm f hf k p
  rw [h_eq]
  have h_cont : Continuous (Function.uncurry
      fun (p : Fin 1 → Fin 4 → ℝ) (t : ℝ) => hadamardIntegrandFDeriv f k t p) :=
    continuous_hadamardIntegrandFDeriv f hf k
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' h_cont 0 1

omit [Fintype ι] [DecidableEq ι] in
lemma contDiffOne_hadamardTerm (f : (Fin 1 → Fin 4 → ℝ) → ℂ)
    (hf : ContDiff ℝ ⊤ f) (k : Fin 4) :
    ContDiff ℝ 1 (hadamardTerm f k) :=
  contDiff_one_iff_fderiv.mpr
    ⟨differentiable_hadamardTerm f hf k, continuous_fderiv_hadamardTerm f hf k⟩

omit [Fintype ι] [DecidableEq ι] in
lemma minkowskiFourier_shift_one (h h' : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) (a : Fin 4 → ℝ)
    (h_shift : ∀ x, h' (fun i => x i + a) = h x) (p : Fin 1 → Fin 4 → ℝ) :
    minkowskiFourier h' p =
      Complex.exp (-(Complex.I * ((minkowskiInner (p 0) a : ℝ) : ℂ))) *
        minkowskiFourier h p := by
  dsimp [minkowskiFourier]
  let v0 : Fin 1 → Fin 4 → ℝ := fun _ => a
  have h_int := MeasureTheory.integral_add_right_eq_self
    (μ := (MeasureTheory.MeasureSpace.volume : MeasureTheory.Measure (Fin 1 → Fin 4 → ℝ)))
    (fun y : Fin 1 → Fin 4 → ℝ =>
      h' y * Complex.exp (-(Complex.I * ((∑ k, minkowskiInner (p k) (y k) : ℝ) : ℂ)))) v0
  rw [← h_int, ← MeasureTheory.integral_const_mul]
  congr 1
  ext x
  have hx_add : x + v0 = fun i => x i + a := rfl
  have h_h' : h' (x + v0) = h x := by
    rw [hx_add]
    exact h_shift x
  dsimp
  rw [h_h']
  have h_sum : (∑ k : Fin 1, minkowskiInner (p k) (x k + v0 k)) =
      (∑ k : Fin 1, minkowskiInner (p k) (x k)) + minkowskiInner (p 0) a := by
    rw [Fin.sum_univ_one, Fin.sum_univ_one]
    have hv0 : v0 0 = a := rfl
    rw [hv0]
    simp [minkowskiInner_explicit]
    ring
  have h_exp_eq :
      (-(Complex.I * ((∑ k, minkowskiInner (p k) (x k) : ℝ) : ℂ)) +
        - (Complex.I * ((minkowskiInner (p 0) a : ℝ) : ℂ))) =
      (- (Complex.I * ((minkowskiInner (p 0) a : ℝ) : ℂ))) +
        (-(Complex.I * ((∑ k, minkowskiInner (p k) (x k) : ℝ) : ℂ))) := by ring
  have h_exp :
      -(Complex.I * (((∑ k : Fin 1, minkowskiInner (p k) (x k)) +
        minkowskiInner (p 0) a : ℝ) : ℂ)) =
      (- (Complex.I * ((minkowskiInner (p 0) a : ℝ) : ℂ))) +
        (-(Complex.I * ((∑ k, minkowskiInner (p k) (x k) : ℝ) : ℂ))) := by
    push_cast
    ring
  rw [h_sum, h_exp, Complex.exp_add]
  ring

omit [Fintype ι] [DecidableEq ι] in
lemma antilipschitzWith_sub_const (v0 : Fin 1 → Fin 4 → ℝ) :
    AntilipschitzWith 1 (fun x : Fin 1 → Fin 4 → ℝ => x - v0) := by
  rw [antilipschitzWith_iff_le_mul_dist]
  intro x y
  rw [NNReal.coe_one, one_mul]
  simp [dist_eq_norm]

omit [Fintype ι] [DecidableEq ι] in
lemma hasTemperateGrowth_sub_const (v0 : Fin 1 → Fin 4 → ℝ) :
    Function.HasTemperateGrowth (fun x : Fin 1 → Fin 4 → ℝ => x - v0) :=
  Function.HasTemperateGrowth.sub
    Function.HasTemperateGrowth.id (Function.HasTemperateGrowth.const v0)

omit [Fintype ι] [DecidableEq ι] in
noncomputable def schwartzTranslate (v0 : Fin 1 → Fin 4 → ℝ) :
    SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ →L[ℂ] SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ :=
  SchwartzMap.compCLMOfAntilipschitz ℂ (hasTemperateGrowth_sub_const v0)
    (antilipschitzWith_sub_const v0)

omit [Fintype ι] [DecidableEq ι] in
lemma schwartzTranslate_apply (v0 : Fin 1 → Fin 4 → ℝ)
    (h : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) (x : Fin 1 → Fin 4 → ℝ) :
    schwartzTranslate v0 h x = h (x - v0) := rfl

omit [Fintype ι] [DecidableEq ι] in
lemma schwartzTranslate_shift (b : Fin 4 → ℝ)
    (h : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) (x : Fin 1 → Fin 4 → ℝ) :
    schwartzTranslate (fun _ => b) h (fun i => x i + b) = h x := by
  rw [schwartzTranslate_apply]
  have h_sub : (fun i : Fin 1 => x i + b) - (fun _ => b) = x := by
    ext i μ
    simp
  rw [h_sub]

omit [Fintype ι] [DecidableEq ι] in
lemma minkowskiFourier_schwartzTranslate_sub (b : Fin 4 → ℝ)
    (h : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) (p : Fin 1 → Fin 4 → ℝ) :
    minkowskiFourier (schwartzTranslate (fun _ => b) h - h) p =
      (Complex.exp (-(Complex.I * ((minkowskiInner (p 0) b : ℝ) : ℂ))) - 1) *
        minkowskiFourier h p := by
  rw [minkowskiFourier_sub]
  have h_shift := schwartzTranslate_shift b h
  rw [minkowskiFourier_shift_one h (schwartzTranslate (fun _ => b) h) b h_shift p]
  ring

omit [Fintype ι] [DecidableEq ι] in
noncomputable def sincDenom (t : ℝ) : ℂ :=
  ∫ s in (0:ℝ)..1, Complex.exp (- (Complex.I * ((s * t : ℝ) : ℂ)))

omit [Fintype ι] [DecidableEq ι] in
lemma sincDenom_mul (t : ℝ) :
    (- Complex.I * (t : ℂ)) * sincDenom t =
      Complex.exp (- (Complex.I * (t : ℂ))) - 1 := by
  dsimp [sincDenom]
  rw [← intervalIntegral.integral_const_mul]
  let F : ℝ → ℂ := fun s => Complex.exp (- (Complex.I * ((s * t : ℝ) : ℂ)))
  have hF_deriv : ∀ s ∈ Set.uIcc (0:ℝ) 1,
      HasDerivAt F
        ((- Complex.I * (t : ℂ)) * Complex.exp (- (Complex.I * ((s * t : ℝ) : ℂ)))) s := by
    intro s _hs
    have h_lin : HasDerivAt (fun s : ℝ => - (Complex.I * ((s * t : ℝ) : ℂ)))
        (- Complex.I * (t : ℂ)) s := by
      have h1 : HasDerivAt (fun s : ℝ => s) 1 s := hasDerivAt_id s
      have h2 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 s := Complex.ofRealCLM.hasDerivAt
      have h3 : HasDerivAt (fun s : ℝ => ((s * t : ℝ) : ℂ)) (t : ℂ) s := by
        have h_eq : (fun s : ℝ => ((s * t : ℝ) : ℂ)) = fun s : ℝ => (s : ℂ) * (t : ℂ) := by
          ext; push_cast; ring
        rw [h_eq]
        simpa using h2.mul_const (t : ℂ)
      have h4 := h3.const_mul (- Complex.I)
      have h_eq2 : (fun s : ℝ => - (Complex.I * ((s * t : ℝ) : ℂ))) =
          fun s : ℝ => (- Complex.I) * (((s * t : ℝ) : ℂ)) := by
        ext; ring
      rw [h_eq2]
      exact h4
    simpa [F, mul_comm] using h_lin.cexp
  have h_int : IntervalIntegrable
      (fun s => (- Complex.I * (t : ℂ)) * Complex.exp (- (Complex.I * ((s * t : ℝ) : ℂ))))
      volume 0 1 := by
    apply Continuous.intervalIntegrable
    continuity
  have h_ftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s hs => hF_deriv s hs) h_int
  rw [h_ftc]
  dsimp [F]
  have h1 : (1 : ℝ) * t = t := one_mul t
  rw [h1]
  have h0 : (0 : ℝ) * t = 0 := zero_mul t
  rw [h0]
  push_cast
  rw [mul_zero, neg_zero, Complex.exp_zero]

omit [Fintype ι] [DecidableEq ι] in
lemma sincDenom_re (t : ℝ) :
    (sincDenom t).re = ∫ s in (0:ℝ)..1, Real.cos (s * t) := by
  dsimp [sincDenom]
  have h_cont : Continuous (fun s : ℝ => Complex.exp (- (Complex.I * ((s * t : ℝ) : ℂ)))) := by
    continuity
  have h_int := h_cont.intervalIntegrable (μ := volume) 0 1
  change Complex.reCLM (∫ s in (0:ℝ)..1, Complex.exp (- (Complex.I * ((s * t : ℝ) : ℂ)))) = _
  rw [(Complex.reCLM.intervalIntegral_comp_comm h_int).symm]
  congr 1
  ext s
  have h_eq : - (Complex.I * ((s * t : ℝ) : ℂ)) = (((- (s * t) : ℝ) : ℂ) * Complex.I) := by
    push_cast; ring
  rw [h_eq]
  exact (Complex.exp_ofReal_mul_I_re (- (s * t))).trans (Real.cos_neg (s * t))

omit [Fintype ι] [DecidableEq ι] in
lemma sincDenom_ne_zero (t : ℝ) (ht : |t| < 1) : sincDenom t ≠ 0 := by
  intro h_zero
  have h_re_zero : (sincDenom t).re = 0 := by rw [h_zero, Complex.zero_re]
  rw [sincDenom_re] at h_re_zero
  have hpi : (1 : ℝ) < Real.pi / 2 := by
    have h3 := Real.pi_gt_three
    linarith
  have h_cos_pos : ∀ s ∈ Set.Icc (0:ℝ) 1, 0 < Real.cos (s * t) := by
    intro s hs
    have hs_nonneg : 0 ≤ s := hs.1
    have hs_le : s ≤ 1 := hs.2
    have h_abs : |s * t| < Real.pi / 2 := by
      rw [abs_mul, abs_of_nonneg hs_nonneg]
      have h1 : s * |t| ≤ 1 * |t| := mul_le_mul_of_nonneg_right hs_le (abs_nonneg t)
      rw [one_mul] at h1
      exact h1.trans_lt (ht.trans hpi)
    rw [abs_lt] at h_abs
    exact Real.cos_pos_of_mem_Ioo ⟨h_abs.1, h_abs.2⟩
  have h_int_pos : 0 < ∫ s in (0:ℝ)..1, Real.cos (s * t) := by
    apply intervalIntegral.integral_pos zero_lt_one
    · exact (Real.continuous_cos.comp (continuous_id.mul continuous_const)).continuousOn
    · intro s hs
      exact (h_cos_pos s (Set.Ioc_subset_Icc_self hs)).le
    · refine ⟨0, ⟨le_rfl, zero_le_one⟩, ?_⟩
      exact h_cos_pos 0 ⟨le_rfl, zero_le_one⟩
  linarith

omit [Fintype ι] [DecidableEq ι] in
noncomputable def sincFactor (t : ℝ) : ℂ :=
  Complex.I / sincDenom t

omit [Fintype ι] [DecidableEq ι] in
lemma exp_sub_one_mul_sincFactor (t : ℝ) (ht : |t| < 1) :
    (Complex.exp (- (Complex.I * (t : ℂ))) - 1) * sincFactor t = (t : ℂ) := by
  dsimp [sincFactor]
  rw [← sincDenom_mul t]
  have h_ne := sincDenom_ne_zero t ht
  have h_cancel : sincDenom t * (Complex.I / sincDenom t) = Complex.I :=
    mul_div_cancel₀ Complex.I h_ne
  calc (- Complex.I * (t : ℂ) * sincDenom t) * (Complex.I / sincDenom t)
    _ = (- Complex.I * (t : ℂ)) * (sincDenom t * (Complex.I / sincDenom t)) := by ring
    _ = (- Complex.I * (t : ℂ)) * Complex.I := by rw [h_cancel]
    _ = (t : ℂ) := by
      have : Complex.I * Complex.I = -1 := Complex.I_mul_I
      linear_combination - (t : ℂ) * this

def basisDisplacement (k : Fin 4) : Fin 4 → ℝ :=
  fun μ => if μ = 0 then (if k = 0 then 1 else 0)
           else if μ = k then -1 else 0

omit [Fintype ι] [DecidableEq ι] in
lemma minkowskiInner_basisDisplacement (v : Fin 4 → ℝ) (k : Fin 4) :
    minkowskiInner v (basisDisplacement k) = v k := by
  rw [minkowskiInner_explicit]
  fin_cases k
  · dsimp [basisDisplacement]; ring
  · dsimp [basisDisplacement]; ring
  · dsimp [basisDisplacement]; ring
  · dsimp [basisDisplacement]; ring

omit [Fintype ι] [DecidableEq ι] in
noncomputable def scaledIntegral (m : ℕ) (G : (Fin 1 → Fin 4 → ℝ) → ℂ)
    (p : Fin 1 → Fin 4 → ℝ) : ℂ :=
  ∫ t in (0:ℝ)..1, ((t ^ m : ℝ) : ℂ) * G (t • p)

omit [Fintype ι] [DecidableEq ι] in
lemma scaledIntegral_zero (G : (Fin 1 → Fin 4 → ℝ) → ℂ) (p : Fin 1 → Fin 4 → ℝ) :
    scaledIntegral 0 G p = ∫ t in (0:ℝ)..1, G (t • p) := by
  dsimp [scaledIntegral]
  simp

omit [Fintype ι] [DecidableEq ι] in
lemma hadamardTerm_eq_scaledIntegral (f : (Fin 1 → Fin 4 → ℝ) → ℂ) (k : Fin 4)
    (p : Fin 1 → Fin 4 → ℝ) :
    hadamardTerm f k p = scaledIntegral 0 (fun q => fderiv ℝ f q (stdBasis k)) p := by
  dsimp [hadamardTerm, scaledIntegral]
  simp

omit [Fintype ι] [DecidableEq ι] in
lemma continuous_scaledIntegrand (m : ℕ) (G : (Fin 1 → Fin 4 → ℝ) → ℂ) (hG : Continuous G) :
    Continuous (fun (pt : (Fin 1 → Fin 4 → ℝ) × ℝ) =>
      ((pt.2 ^ m : ℝ) : ℂ) * G (pt.2 • pt.1)) := by
  have h_t : Continuous (fun (pt : (Fin 1 → Fin 4 → ℝ) × ℝ) => ((pt.2 ^ m : ℝ) : ℂ)) := by
    exact Complex.ofRealCLM.continuous.comp (continuous_snd.pow m)
  have h_smul : Continuous (fun (pt : (Fin 1 → Fin 4 → ℝ) × ℝ) => pt.2 • pt.1) :=
    continuous_snd.smul continuous_fst
  exact h_t.mul (hG.comp h_smul)

omit [Fintype ι] [DecidableEq ι] in
lemma continuous_scaledIntegral (m : ℕ) (G : (Fin 1 → Fin 4 → ℝ) → ℂ) (hG : Continuous G) :
    Continuous (scaledIntegral m G) := by
  have h_cont : Continuous (Function.uncurry fun (p : Fin 1 → Fin 4 → ℝ) (t : ℝ) =>
      ((t ^ m : ℝ) : ℂ) * G (t • p)) := by
    change Continuous (fun (pt : (Fin 1 → Fin 4 → ℝ) × ℝ) =>
      ((pt.2 ^ m : ℝ) : ℂ) * G (pt.2 • pt.1))
    exact continuous_scaledIntegrand m G hG
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' h_cont 0 1

omit [Fintype ι] [DecidableEq ι] in
noncomputable def scaledIntegrandFDeriv (m : ℕ) (G : (Fin 1 → Fin 4 → ℝ) → ℂ) (t : ℝ)
    (p : Fin 1 → Fin 4 → ℝ) : (Fin 1 → Fin 4 → ℝ) →L[ℝ] ℂ :=
  ((t ^ m : ℝ) : ℂ) • (t • fderiv ℝ G (t • p))

omit [Fintype ι] [DecidableEq ι] in
lemma hasFDerivAt_scaledIntegrand (m : ℕ) (G : (Fin 1 → Fin 4 → ℝ) → ℂ) (hG : ContDiff ℝ 1 G)
    (t : ℝ) (p : Fin 1 → Fin 4 → ℝ) :
    HasFDerivAt (fun q => ((t ^ m : ℝ) : ℂ) * G (t • q))
      (scaledIntegrandFDeriv m G t p) p := by
  let L_t : (Fin 1 → Fin 4 → ℝ) →L[ℝ] (Fin 1 → Fin 4 → ℝ) :=
    t • ContinuousLinearMap.id ℝ (Fin 1 → Fin 4 → ℝ)
  have hG_diff : DifferentiableAt ℝ G (t • p) := hG.differentiable one_ne_zero (t • p)
  have h_chain := HasFDerivAt.comp p hG_diff.hasFDerivAt L_t.hasFDerivAt
  have h_mul := h_chain.const_mul ((t ^ m : ℝ) : ℂ)
  have h_eq : ((t ^ m : ℝ) : ℂ) • ((fderiv ℝ G (t • p)).comp L_t) =
      scaledIntegrandFDeriv m G t p := by
    dsimp [scaledIntegrandFDeriv]
    ext v
    simp [L_t]
  rw [h_eq] at h_mul
  exact h_mul

omit [Fintype ι] [DecidableEq ι] in
lemma continuous_scaledIntegrandFDeriv (m : ℕ) (G : (Fin 1 → Fin 4 → ℝ) → ℂ)
    (hG : ContDiff ℝ 2 G) :
    Continuous (fun (pt : (Fin 1 → Fin 4 → ℝ) × ℝ) => scaledIntegrandFDeriv m G pt.2 pt.1) := by
  have h_cont_dG : Continuous (fderiv ℝ G) := hG.continuous_fderiv two_ne_zero
  have h_smul : Continuous (fun (pt : (Fin 1 → Fin 4 → ℝ) × ℝ) => pt.2 • pt.1) :=
    continuous_snd.smul continuous_fst
  have h_comp_cont : Continuous (fun (pt : (Fin 1 → Fin 4 → ℝ) × ℝ) =>
      fderiv ℝ G (pt.2 • pt.1)) :=
    h_cont_dG.comp h_smul
  have h_t_smul : Continuous (fun (pt : (Fin 1 → Fin 4 → ℝ) × ℝ) =>
      pt.2 • fderiv ℝ G (pt.2 • pt.1)) :=
    continuous_snd.smul h_comp_cont
  have h_tm : Continuous (fun (pt : (Fin 1 → Fin 4 → ℝ) × ℝ) => ((pt.2 ^ m : ℝ) : ℂ)) :=
    Complex.ofRealCLM.continuous.comp (continuous_snd.pow m)
  exact h_tm.smul h_t_smul

omit [Fintype ι] [DecidableEq ι] in
lemma hasFDerivAt_scaledIntegral (m : ℕ) (G : (Fin 1 → Fin 4 → ℝ) → ℂ)
    (hG : ContDiff ℝ 2 G) (p : Fin 1 → Fin 4 → ℝ) :
    HasFDerivAt (scaledIntegral m G)
      (∫ t in (0:ℝ)..1, scaledIntegrandFDeriv m G t p) p := by
  have hs : Metric.ball p 1 ∈ 𝓝 p := Metric.ball_mem_nhds p zero_lt_one
  have hF_meas : ∀ᶠ (x : Fin 1 → Fin 4 → ℝ) in 𝓝 p,
      AEStronglyMeasurable (fun t : ℝ => ((t ^ m : ℝ) : ℂ) * G (t • x))
        (volume.restrict (Ι (0:ℝ) 1)) := by
    refine Filter.Eventually.of_forall (fun x => ?_)
    have h_cont : Continuous (fun t : ℝ => ((t ^ m : ℝ) : ℂ) * G (t • x)) := by
      have h_pair : Continuous (fun t : ℝ => (x, t)) := by fun_prop
      exact (continuous_scaledIntegrand m G hG.continuous).comp h_pair
    exact h_cont.aestronglyMeasurable
  have hF_int : IntervalIntegrable (fun t : ℝ => ((t ^ m : ℝ) : ℂ) * G (t • p))
      volume 0 1 := by
    have h_cont : Continuous (fun t : ℝ => ((t ^ m : ℝ) : ℂ) * G (t • p)) := by
      have h_pair : Continuous (fun t : ℝ => (p, t)) := by fun_prop
      exact (continuous_scaledIntegrand m G hG.continuous).comp h_pair
    exact h_cont.intervalIntegrable 0 1
  have hF'_meas : AEStronglyMeasurable (scaledIntegrandFDeriv m G · p)
      (volume.restrict (Ι (0:ℝ) 1)) := by
    have h_pair : Continuous (fun t : ℝ => (p, t)) := by fun_prop
    have h_cont : Continuous (fun t : ℝ => scaledIntegrandFDeriv m G t p) :=
      (continuous_scaledIntegrandFDeriv m G hG).comp h_pair
    exact h_cont.aestronglyMeasurable
  let K : Set ((Fin 1 → Fin 4 → ℝ) × ℝ) :=
    (Metric.closedBall p 1) ×ˢ (Set.uIcc (0:ℝ) 1)
  have hK_comp : IsCompact K := (isCompact_closedBall p 1).prod isCompact_uIcc
  have h_cont_on : ContinuousOn (fun pt : (Fin 1 → Fin 4 → ℝ) × ℝ =>
      scaledIntegrandFDeriv m G pt.2 pt.1) K :=
    (continuous_scaledIntegrandFDeriv m G hG).continuousOn
  obtain ⟨C, hC⟩ := hK_comp.exists_bound_of_continuousOn h_cont_on
  have h_bound : ∀ᵐ (t : ℝ) ∂volume.restrict (Ι (0:ℝ) 1), ∀ x ∈ Metric.ball p 1,
      ‖scaledIntegrandFDeriv m G t x‖ ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht x hx
    have hx_cl : x ∈ Metric.closedBall p 1 := Metric.ball_subset_closedBall hx
    have ht_icc : t ∈ Set.uIcc (0:ℝ) 1 := Set.uIoc_subset_uIcc ht
    exact hC (x, t) ⟨hx_cl, ht_icc⟩
  have bound_int : IntervalIntegrable (fun _ : ℝ => C) volume 0 1 :=
    intervalIntegrable_const
  have h_diff : ∀ᵐ (t : ℝ) ∂volume.restrict (Ι (0:ℝ) 1), ∀ x ∈ Metric.ball p 1,
      HasFDerivAt (fun q => ((t ^ m : ℝ) : ℂ) * G (t • q))
        (scaledIntegrandFDeriv m G t x) x := by
    refine Filter.Eventually.of_forall (fun t => fun x _hx => ?_)
    exact hasFDerivAt_scaledIntegrand m G (hG.of_le (by norm_num)) t x
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le'' hs hF_meas hF_int hF'_meas
    h_bound bound_int h_diff

omit [Fintype ι] [DecidableEq ι] in
lemma fderiv_scaledIntegral (m : ℕ) (G : (Fin 1 → Fin 4 → ℝ) → ℂ) (hG : ContDiff ℝ 2 G)
    (p : Fin 1 → Fin 4 → ℝ) :
    fderiv ℝ (scaledIntegral m G) p = ∫ t in (0:ℝ)..1, scaledIntegrandFDeriv m G t p :=
  (hasFDerivAt_scaledIntegral m G hG p).fderiv

omit [Fintype ι] [DecidableEq ι] in
lemma differentiable_scaledIntegral (m : ℕ) (G : (Fin 1 → Fin 4 → ℝ) → ℂ)
    (hG : ContDiff ℝ 2 G) :
    Differentiable ℝ (scaledIntegral m G) := fun p =>
  (hasFDerivAt_scaledIntegral m G hG p).differentiableAt

omit [Fintype ι] [DecidableEq ι] in
lemma scaledIntegrandFDeriv_apply (m : ℕ) (G : (Fin 1 → Fin 4 → ℝ) → ℂ) (t : ℝ)
    (p v : Fin 1 → Fin 4 → ℝ) :
    scaledIntegrandFDeriv m G t p v = ((t ^ (m + 1) : ℝ) : ℂ) * fderiv ℝ G (t • p) v := by
  dsimp [scaledIntegrandFDeriv]
  simp only [_root_.smul_apply, Complex.real_smul]
  push_cast
  rw [pow_succ (t : ℂ) m]
  ring

omit [Fintype ι] [DecidableEq ι] in
lemma fderiv_scaledIntegral_apply (m : ℕ) (G : (Fin 1 → Fin 4 → ℝ) → ℂ)
    (hG : ContDiff ℝ 2 G) (p v : Fin 1 → Fin 4 → ℝ) :
    fderiv ℝ (scaledIntegral m G) p v =
      scaledIntegral (m + 1) (fun q => fderiv ℝ G q v) p := by
  rw [fderiv_scaledIntegral m G hG p]
  have h_int : IntervalIntegrable (scaledIntegrandFDeriv m G · p) volume 0 1 := by
    have h_pair : Continuous (fun t : ℝ => (p, t)) := by fun_prop
    exact ((continuous_scaledIntegrandFDeriv m G hG).comp h_pair).intervalIntegrable 0 1
  rw [ContinuousLinearMap.intervalIntegral_apply h_int v]
  dsimp [scaledIntegral]
  congr 1
  ext t
  exact scaledIntegrandFDeriv_apply m G t p v

omit [Fintype ι] [DecidableEq ι] in
lemma contDiff_fderiv_apply_top' (G : (Fin 1 → Fin 4 → ℝ) → ℂ)
    (hG : ContDiff ℝ (⊤ : ℕ∞) G) (v : Fin 1 → Fin 4 → ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q => fderiv ℝ G q v) := by
  let L : ((Fin 1 → Fin 4 → ℝ) →L[ℝ] ℂ) →L[ℝ] ℂ := ContinuousLinearMap.apply ℝ ℂ v
  have h_comp : (fun q => fderiv ℝ G q v) = L ∘ (fderiv ℝ G) := rfl
  rw [h_comp]
  exact L.contDiff.comp (hG.fderiv_right le_rfl)

omit [Fintype ι] [DecidableEq ι] in
lemma contDiff_scaledIntegral_nat (n : ℕ) :
    ∀ (m : ℕ) (G : (Fin 1 → Fin 4 → ℝ) → ℂ),
      ContDiff ℝ (⊤ : ℕ∞) G → ContDiff ℝ (n : ℕ) (scaledIntegral m G) := by
  induction n with
  | zero =>
    intro m G hG
    rw [Nat.cast_zero, contDiff_zero]
    exact continuous_scaledIntegral m G hG.continuous
  | succ n ih =>
    intro m G hG
    rw [Nat.cast_succ, contDiff_succ_iff_fderiv_apply]
    refine ⟨differentiable_scaledIntegral m G (hG.of_le (by decide)), ?_, ?_⟩
    · intro h_omega
      have : (n : ℕ∞ω) ≠ ω := by simp
      contradiction
    · intro v
      have h_eq : (fun x => fderiv ℝ (scaledIntegral m G) x v) =
          scaledIntegral (m + 1) (fun q => fderiv ℝ G q v) := by
        funext x
        exact fderiv_scaledIntegral_apply m G (hG.of_le (by decide)) x v
      rw [h_eq]
      exact ih (m + 1) (fun q => fderiv ℝ G q v) (contDiff_fderiv_apply_top' G hG v)

omit [Fintype ι] [DecidableEq ι] in
lemma contDiffTop_scaledIntegral (m : ℕ) (G : (Fin 1 → Fin 4 → ℝ) → ℂ)
    (hG : ContDiff ℝ (⊤ : ℕ∞) G) :
    ContDiff ℝ (⊤ : ℕ∞) (scaledIntegral m G) := by
  rw [contDiff_infty]
  intro n
  exact contDiff_scaledIntegral_nat n m G hG

omit [Fintype ι] [DecidableEq ι] in
lemma contDiffTop_hadamardTerm (f : (Fin 1 → Fin 4 → ℝ) → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (k : Fin 4) :
    ContDiff ℝ (⊤ : ℕ∞) (hadamardTerm f k) := by
  have h_eq : hadamardTerm f k =
      scaledIntegral 0 (fun q => fderiv ℝ f q (stdBasis k)) := by
    funext p
    exact hadamardTerm_eq_scaledIntegral f k p
  rw [h_eq]
  apply contDiffTop_scaledIntegral
  exact contDiff_fderiv_apply_top' f hf (stdBasis k)

omit [Fintype ι] [DecidableEq ι] in
lemma contDiffTop_sincDenom_comp (k : Fin 4) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : Fin 1 → Fin 4 → ℝ => sincDenom (p 0 k)) := by
  have h_eq : (fun p : Fin 1 → Fin 4 → ℝ => sincDenom (p 0 k)) =
      scaledIntegral 0 (fun q => Complex.exp (- (Complex.I * ((q 0 k : ℝ) : ℂ)))) := by
    funext p
    dsimp [sincDenom, scaledIntegral]
    congr 1
    ext s
    simp only [pow_zero, Complex.ofReal_one, one_mul]
  rw [h_eq]
  apply contDiffTop_scaledIntegral
  have h_lin : ContDiff ℝ (⊤ : ℕ∞) (fun q : Fin 1 → Fin 4 → ℝ => q 0 k) := by fun_prop
  have h_c : ContDiff ℝ (⊤ : ℕ∞) (fun q : Fin 1 → Fin 4 → ℝ => ((q 0 k : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp h_lin
  have h_mul : ContDiff ℝ (⊤ : ℕ∞)
      (fun q : Fin 1 → Fin 4 → ℝ => - (Complex.I * ((q 0 k : ℝ) : ℂ))) :=
    (contDiff_const.mul h_c).neg
  exact Complex.contDiff_exp.comp h_mul

def cutoffBump12 : ContDiffBump (0 : Fin 1 → Fin 4 → ℝ) where
  rIn := 1
  rOut := 1.2
  rIn_pos := zero_lt_one
  rIn_lt_rOut := by norm_num

omit [Fintype ι] [DecidableEq ι] in
noncomputable def sincDenomReg (k : Fin 4) (p : Fin 1 → Fin 4 → ℝ) : ℂ :=
  sincDenom (p 0 k) + 3 * (1 - ((cutoffBump12 p : ℝ) : ℂ))

omit [Fintype ι] [DecidableEq ι] in
lemma sincDenomReg_eq (k : Fin 4) (p : Fin 1 → Fin 4 → ℝ) (hp : p ∈ Metric.ball 0 1) :
    sincDenomReg k p = sincDenom (p 0 k) := by
  dsimp [sincDenomReg]
  have hp_cl : p ∈ Metric.closedBall 0 1 := Metric.ball_subset_closedBall hp
  have h_bump : cutoffBump12 p = 1 := cutoffBump12.one_of_mem_closedBall hp_cl
  rw [h_bump]
  push_cast
  ring

omit [Fintype ι] [DecidableEq ι] in
lemma sincDenom_re_pos_of_lt_pi_div_two (t : ℝ) (ht : |t| < Real.pi / 2) :
    0 < (sincDenom t).re := by
  rw [sincDenom_re]
  have h_cos_pos : ∀ s ∈ Set.Icc (0:ℝ) 1, 0 < Real.cos (s * t) := by
    intro s hs
    have hs_nonneg : 0 ≤ s := hs.1
    have hs_le : s ≤ 1 := hs.2
    have h_abs : |s * t| < Real.pi / 2 := by
      rw [abs_mul, abs_of_nonneg hs_nonneg]
      have h1 : s * |t| ≤ 1 * |t| := mul_le_mul_of_nonneg_right hs_le (abs_nonneg t)
      rw [one_mul] at h1
      exact h1.trans_lt ht
    rw [abs_lt] at h_abs
    exact Real.cos_pos_of_mem_Ioo ⟨h_abs.1, h_abs.2⟩
  apply intervalIntegral.integral_pos zero_lt_one
  · exact (Real.continuous_cos.comp (continuous_id.mul continuous_const)).continuousOn
  · intro s hs
    exact (h_cos_pos s (Set.Ioc_subset_Icc_self hs)).le
  · refine ⟨0, ⟨le_rfl, zero_le_one⟩, ?_⟩
    exact h_cos_pos 0 ⟨le_rfl, zero_le_one⟩

omit [Fintype ι] [DecidableEq ι] in
lemma sincDenom_re_ge_neg_one (t : ℝ) : -1 ≤ (sincDenom t).re := by
  rw [sincDenom_re]
  have h_le : (∫ s in (0:ℝ)..1, (-1 : ℝ)) ≤ ∫ s in (0:ℝ)..1, Real.cos (s * t) := by
    apply intervalIntegral.integral_mono_on zero_le_one
    · exact intervalIntegrable_const
    · exact (Real.continuous_cos.comp (continuous_id.mul continuous_const)).intervalIntegrable 0 1
    · intro s _hs
      exact Real.neg_one_le_cos (s * t)
  simp only [intervalIntegral.integral_const, sub_zero, one_smul] at h_le
  exact h_le

omit [Fintype ι] [DecidableEq ι] in
lemma sincDenomReg_ne_zero (k : Fin 4) (p : Fin 1 → Fin 4 → ℝ) : sincDenomReg k p ≠ 0 := by
  intro h_zero
  apply_fun Complex.re at h_zero
  rw [Complex.zero_re] at h_zero
  dsimp [sincDenomReg] at h_zero
  have h_re_part : 3 * (1 - ((cutoffBump12 p : ℝ) : ℂ)) =
      (((3 * (1 - cutoffBump12 p) : ℝ) : ℂ)) := by
    push_cast
    ring
  rw [h_re_part, Complex.ofReal_re] at h_zero
  have h_bump_le : cutoffBump12 p ≤ 1 := cutoffBump12.le_one
  have h_sub_nonneg : 0 ≤ 1 - cutoffBump12 p := sub_nonneg.mpr h_bump_le
  by_cases hp_norm : ‖p‖ < 1.2
  · have hpk : |p 0 k| < Real.pi / 2 := by
      have h1 : |p 0 k| ≤ ‖p‖ := by
        have h_proj : ‖p 0 k‖ ≤ ‖p 0‖ := norm_le_pi_norm (p 0) k
        have h_proj0 : ‖p 0‖ ≤ ‖p‖ := norm_le_pi_norm p 0
        exact h_proj.trans h_proj0
      have hpi : (1.2 : ℝ) < Real.pi / 2 := by
        have h3 := Real.pi_gt_three
        linarith
      exact (h1.trans_lt hp_norm).trans hpi
    have h_pos := sincDenom_re_pos_of_lt_pi_div_two (p 0 k) hpk
    have h_nonneg : 0 ≤ 3 * (1 - cutoffBump12 p) := mul_nonneg (by norm_num) h_sub_nonneg
    linarith
  · have hp_dist : 1.2 ≤ dist p 0 := by
      rw [dist_zero_right]
      linarith
    have h_zero_bump : cutoffBump12 p = 0 := cutoffBump12.zero_of_le_dist hp_dist
    have h_ge := sincDenom_re_ge_neg_one (p 0 k)
    rw [h_zero_bump] at h_zero
    linarith

omit [Fintype ι] [DecidableEq ι] in
lemma contDiffTop_sincDenomReg (k : Fin 4) :
    ContDiff ℝ (⊤ : ℕ∞) (sincDenomReg k) := by
  change ContDiff ℝ (⊤ : ℕ∞) (fun p : Fin 1 → Fin 4 → ℝ =>
    sincDenom (p 0 k) + 3 * (1 - ((cutoffBump12 p : ℝ) : ℂ)))
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun p : Fin 1 → Fin 4 → ℝ => sincDenom (p 0 k)) :=
    contDiffTop_sincDenom_comp k
  have h_bump : ContDiff ℝ (⊤ : ℕ∞) (fun p : Fin 1 → Fin 4 → ℝ => ((cutoffBump12 p : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp cutoffBump12.contDiff
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun p : Fin 1 → Fin 4 → ℝ =>
      (3 : ℂ) * (1 - ((cutoffBump12 p : ℝ) : ℂ))) :=
    contDiff_const.mul (contDiff_const.sub h_bump)
  exact h1.add h2

omit [Fintype ι] [DecidableEq ι] in
noncomputable def sincFactorReg (k : Fin 4) (p : Fin 1 → Fin 4 → ℝ) : ℂ :=
  Complex.I / sincDenomReg k p

omit [Fintype ι] [DecidableEq ι] in
lemma sincFactorReg_eq (k : Fin 4) (p : Fin 1 → Fin 4 → ℝ) (hp : p ∈ Metric.ball 0 1) :
    sincFactorReg k p = sincFactor (p 0 k) := by
  dsimp [sincFactorReg, sincFactor]
  rw [sincDenomReg_eq k p hp]

omit [Fintype ι] [DecidableEq ι] in
lemma contDiffTop_sincFactorReg (k : Fin 4) :
    ContDiff ℝ (⊤ : ℕ∞) (sincFactorReg k) := by
  have h_eq : sincFactorReg k =
      (fun p : Fin 1 → Fin 4 → ℝ => Complex.I * (sincDenomReg k p)⁻¹) := by
    ext p
    dsimp [sincFactorReg]
    ring
  rw [h_eq]
  have h_inv : ContDiff ℝ (⊤ : ℕ∞) (fun p : Fin 1 → Fin 4 → ℝ => (sincDenomReg k p)⁻¹) :=
    (contDiffTop_sincDenomReg k).inv (sincDenomReg_ne_zero k)
  exact contDiff_const.mul h_inv

omit [Fintype ι] [DecidableEq ι] in
noncomputable def minkowskiFourierSchwartzMap (g : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) :
    SchwartzMap (EuclideanSpace ℝ (Fin 1 × Fin 4)) ℂ :=
  (SchwartzMap.fourierTransformCLM ℂ)
    ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (piSpaceEquiv 1).symm)
      ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (minkowskiFlipEquiv 1)) g))

omit [Fintype ι] [DecidableEq ι] in
noncomputable def posScaledMomentumCLM :
    (Fin 1 → Fin 4 → ℝ) →L[ℝ] (Fin 1 → Fin 4 → ℝ) :=
  (2 * Real.pi)⁻¹ • ContinuousLinearMap.id ℝ (Fin 1 → Fin 4 → ℝ)

omit [Fintype ι] [DecidableEq ι] in
noncomputable def momentumToEuclidCLM :
    (Fin 1 → Fin 4 → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin 1 × Fin 4) :=
  (piSpaceEquiv 1).toContinuousLinearMap.comp posScaledMomentumCLM

omit [Fintype ι] [DecidableEq ι] in
lemma minkowskiFourier_eq_schwartzMap (g : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ)
    (p : Fin 1 → Fin 4 → ℝ) :
    minkowskiFourier g p = (minkowskiFourierSchwartzMap g) (momentumToEuclidCLM p) := by
  have h_meas := measurePreserving_minkowskiFlip_piSpace_one
  have h_emb := measurableEmbedding_minkowskiFlip_piSpace_one
  have h_fourier_coe : ((minkowskiFourierSchwartzMap g) : EuclideanSpace ℝ (Fin 1 × Fin 4) → ℂ) =
      𝓕 (((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (piSpaceEquiv 1).symm)
        ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (minkowskiFlipEquiv 1)) g)) :
          EuclideanSpace ℝ (Fin 1 × Fin 4) → ℂ) :=
    SchwartzMap.fourier_coe _
  have h_rhs : (minkowskiFourierSchwartzMap g) (momentumToEuclidCLM p) =
      𝓕 (((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (piSpaceEquiv 1).symm)
        ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (minkowskiFlipEquiv 1)) g)) :
          EuclideanSpace ℝ (Fin 1 × Fin 4) → ℂ) (momentumToEuclidCLM p) := by
    rw [← h_fourier_coe]
  rw [h_rhs, Real.fourier_eq]
  dsimp [minkowskiFourier]
  have h_comp := (MeasurePreserving.integral_comp h_meas h_emb
    (fun u : EuclideanSpace ℝ (Fin 1 × Fin 4) =>
      ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (piSpaceEquiv 1).symm)
        ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (minkowskiFlipEquiv 1)) g)) u *
        Real.fourierChar (- inner ℝ u (piSpaceEquiv 1 (posScaledMomentum p))))).symm
  have h_integrand : (fun x : Fin 1 → Fin 4 → ℝ =>
      g x * Complex.exp (-(Complex.I * ((∑ k : Fin 1, minkowskiInner (p k) (x k) : ℝ) : ℂ)))) =
      (fun x =>
        ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (piSpaceEquiv 1).symm)
          ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (minkowskiFlipEquiv 1)) g))
            (piSpaceEquiv 1 (minkowskiFlipFun 1 x)) *
          Real.fourierChar (- inner ℝ (piSpaceEquiv 1 (minkowskiFlipFun 1 x))
            (piSpaceEquiv 1 (posScaledMomentum p)))) := by
    ext x
    congr 1
    · dsimp [SchwartzMap.compCLMOfContinuousLinearEquiv]
      have h1 : (piSpaceEquiv 1).symm (piSpaceEquiv 1 (minkowskiFlipFun 1 x)) =
          minkowskiFlipFun 1 x := (piSpaceEquiv 1).symm_apply_apply _
      rw [h1]
      have h2 : (minkowskiFlipEquiv 1) (minkowskiFlipFun 1 x) = x :=
        minkowskiFlipFun_involutive 1 x
      rw [h2]
    · have h_phase := fourier_phase_eq p x
      simp only [Real.fourierChar_apply]
      have h_eq : -(Complex.I * ((∑ k, minkowskiInner (p k) (x k) : ℝ) : ℂ)) =
          (((-2 * Real.pi * inner ℝ (piSpaceEquiv 1 (minkowskiFlipFun 1 x))
            (piSpaceEquiv 1 (posScaledMomentum p)) : ℝ) : ℂ) * Complex.I) := by
        simp only [Fin.sum_univ_one]
        rw [h_phase]
        push_cast
        ring
      rw [h_eq]
      congr 1
      push_cast
      ring
  rw [h_integrand, ← h_comp]
  dsimp [momentumToEuclidCLM, posScaledMomentumCLM, SchwartzMap.compCLMOfContinuousLinearEquiv]
  congr 1
  ext v
  rw [mul_comm]
  rfl

omit [Fintype ι] [DecidableEq ι] in
lemma contDiffTop_minkowskiFourier (g : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (minkowskiFourier g) := by
  have h_eq : minkowskiFourier g =
      (minkowskiFourierSchwartzMap g) ∘ momentumToEuclidCLM := by
    ext p
    exact minkowskiFourier_eq_schwartzMap g p
  rw [h_eq]
  exact (minkowskiFourierSchwartzMap g).smooth'.comp momentumToEuclidCLM.contDiff

omit [Fintype ι] [DecidableEq ι] in
noncomputable def psiFun (g : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) (k : Fin 4)
    (p : Fin 1 → Fin 4 → ℝ) : ℂ :=
  ((cutoffBump12 p : ℝ) : ℂ) * (sincFactorReg k p * hadamardTerm (minkowskiFourier g) k p)

omit [Fintype ι] [DecidableEq ι] in
lemma contDiffTop_psiFun (g : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) (k : Fin 4) :
    ContDiff ℝ (⊤ : ℕ∞) (psiFun g k) := by
  change ContDiff ℝ (⊤ : ℕ∞) (fun p : Fin 1 → Fin 4 → ℝ =>
    ((cutoffBump12 p : ℝ) : ℂ) * (sincFactorReg k p * hadamardTerm (minkowskiFourier g) k p))
  have h_bump : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : Fin 1 → Fin 4 → ℝ => ((cutoffBump12 p : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp cutoffBump12.contDiff
  have h_sinc : ContDiff ℝ (⊤ : ℕ∞) (sincFactorReg k) :=
    contDiffTop_sincFactorReg k
  have h_g : ContDiff ℝ (⊤ : ℕ∞) (minkowskiFourier g) :=
    contDiffTop_minkowskiFourier g
  have h_hadamard : ContDiff ℝ (⊤ : ℕ∞) (hadamardTerm (minkowskiFourier g) k) :=
    contDiffTop_hadamardTerm (minkowskiFourier g) h_g k
  exact h_bump.mul (h_sinc.mul h_hadamard)

omit [Fintype ι] [DecidableEq ι] in
lemma hasCompactSupport_psiFun (g : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) (k : Fin 4) :
    HasCompactSupport (psiFun g k) := by
  have h_supp : HasCompactSupport
      (fun p : Fin 1 → Fin 4 → ℝ => ((cutoffBump12 p : ℝ) : ℂ)) := by
    have h1 := cutoffBump12.hasCompactSupport
    exact h1.comp_left (g := fun (r : ℝ) => (r : ℂ)) Complex.ofReal_zero
  exact h_supp.mul_right

omit [Fintype ι] [DecidableEq ι] in
noncomputable def psiSchwartz (g : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) (k : Fin 4) :
    SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ :=
  (hasCompactSupport_psiFun g k).toSchwartzMap (contDiffTop_psiFun g k)

omit [Fintype ι] [DecidableEq ι] in
noncomputable def invScaledMomentumEquiv :
    (Fin 1 → Fin 4 → ℝ) ≃L[ℝ] (Fin 1 → Fin 4 → ℝ) where
  toFun q := (- (2 * Real.pi)) • q
  invFun p := (- (2 * Real.pi)⁻¹) • p
  left_inv q := by
    simp only [smul_smul]
    have hpi : (2 * Real.pi) ≠ 0 := by positivity
    have : (- (2 * Real.pi)⁻¹) * (- (2 * Real.pi)) = 1 := by
      rw [neg_mul_neg, inv_mul_cancel₀ hpi]
    rw [this, one_smul]
  right_inv p := by
    simp only [smul_smul]
    have hpi : (2 * Real.pi) ≠ 0 := by positivity
    have : (- (2 * Real.pi)) * (- (2 * Real.pi)⁻¹) = 1 := by
      rw [neg_mul_neg, mul_inv_cancel₀ hpi]
    rw [this, one_smul]
  map_add' x y := smul_add _ x y
  map_smul' c x := smul_comm _ c x
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

omit [Fintype ι] [DecidableEq ι] in
lemma invScaledMomentumEquiv_apply_scaledMomentum (p : Fin 1 → Fin 4 → ℝ) :
    invScaledMomentumEquiv (scaledMomentum p) = p := by
  dsimp [scaledMomentum, invScaledMomentumEquiv]
  simp only [smul_smul]
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  have : (- (2 * Real.pi)) * (- (2 * Real.pi)⁻¹) = 1 := by
    rw [neg_mul_neg, mul_inv_cancel₀ hpi]
  rw [this, one_smul]

omit [Fintype ι] [DecidableEq ι] in
noncomputable def psiSchwartzScaled (g : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) (k : Fin 4) :
    SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ invScaledMomentumEquiv (psiSchwartz g k)

omit [Fintype ι] [DecidableEq ι] in
lemma psiSchwartzScaled_apply_scaledMomentum (g : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) (k : Fin 4)
    (p : Fin 1 → Fin 4 → ℝ) :
    (psiSchwartzScaled g k) (scaledMomentum p) = (psiSchwartz g k) p := by
  dsimp [psiSchwartzScaled]
  congr 1
  exact invScaledMomentumEquiv_apply_scaledMomentum p

omit [Fintype ι] [DecidableEq ι] in
lemma minkowskiFourier_sum {m : ℕ} (F : Fin m → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ)
    (p : Fin 1 → Fin 4 → ℝ) :
    minkowskiFourier (∑ j, F j) p = ∑ j, minkowskiFourier (F j) p := by
  dsimp [minkowskiFourier]
  have h_sum : (fun x : Fin 1 → Fin 4 → ℝ => (∑ j, F j) x *
      Complex.exp (-(Complex.I * ((∑ k, minkowskiInner (p k) (x k) : ℝ) : ℂ)))) =
      (fun x => ∑ j, (F j x *
        Complex.exp (-(Complex.I * ((∑ k, minkowskiInner (p k) (x k) : ℝ) : ℂ))))) := by
    ext x
    simp only [_root_.sum_apply, Finset.sum_mul]
  rw [h_sum]
  exact integral_finsetSum Finset.univ (fun j _ => integrable_f_mul_exp_phase 1 (F j) p)

lemma W_one_exists_shift_rep (g : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) (hg : ∫ x, g x = 0) :
    ∃ (m : ℕ) (h : Fin m → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) (a : Fin m → Fin 4 → ℝ)
      (h' : Fin m → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ),
      (∀ j x, h' j (fun i => x i + a j) = h j x) ∧
      (∀ p ∈ Metric.ball (0 : Fin 1 → Fin 4 → ℝ) 1,
        minkowskiFourier g p = minkowskiFourier (∑ j, (h' j - h j)) p) := by
  let m : ℕ := 4
  let a : Fin 4 → Fin 4 → ℝ := basisDisplacement
  let h : Fin 4 → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ := fun k =>
    invMinkowskiFourierCLM 1 (psiSchwartzScaled g k)
  let h' : Fin 4 → SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ := fun k =>
    schwartzTranslate (fun _ => a k) (h k)
  refine ⟨m, h, a, h', ?_, ?_⟩
  · intro j x
    exact schwartzTranslate_shift (a j) (h j) x
  · intro p hp
    rw [minkowskiFourier_sum]
    have hp_norm : ‖p‖ < 1 := by
      rw [Metric.mem_ball, dist_zero_right] at hp
      exact hp
    have hp_cl : p ∈ Metric.closedBall 0 1 := Metric.ball_subset_closedBall hp
    have h_bump : cutoffBump12 p = 1 := cutoffBump12.one_of_mem_closedBall hp_cl
    have h_g0 : minkowskiFourier g 0 = 0 := by
      rw [minkowskiFourier_eval_zero]
      exact hg
    have h_g_top := contDiffTop_minkowskiFourier g
    have h_g_smooth : ∀ t ∈ Set.Icc (0:ℝ) 1, ContDiffAt ℝ 1 (minkowskiFourier g) (t • p) := by
      intro t _ht
      exact (h_g_top.of_le (by decide)).contDiffAt
    have hint : ∀ k : Fin 4, IntervalIntegrable
        (fun t => fderiv ℝ (minkowskiFourier g) (t • p) (stdBasis k)) volume 0 1 := by
      intro k
      have h_cont : Continuous
          (fun t : ℝ => fderiv ℝ (minkowskiFourier g) (t • p) (stdBasis k)) := by
        have h_c1 := contDiff_fderiv_apply_top' (minkowskiFourier g) h_g_top (stdBasis k)
        exact h_c1.continuous.comp (continuous_id.smul continuous_const)
      exact h_cont.intervalIntegrable 0 1
    have h_hadamard := hadamard_identity (minkowskiFourier g) p h_g_smooth h_g0 hint
    rw [h_hadamard]
    congr 1
    ext k
    rw [minkowskiFourier_schwartzTranslate_sub]
    dsimp [h]
    rw [minkowskiFourier_invMinkowskiFourierCLM_one]
    rw [psiSchwartzScaled_apply_scaledMomentum]
    have h_psi_eval : (psiSchwartz g k) p = psiFun g k p := rfl
    rw [h_psi_eval]
    dsimp [psiFun]
    rw [h_bump]
    push_cast
    rw [one_mul]
    rw [sincFactorReg_eq k p hp]
    rw [minkowskiInner_basisDisplacement (p 0) k]
    have hpk : |p 0 k| < 1 := by
      have h1 : |p 0 k| ≤ ‖p‖ := by
        have h_proj : ‖p 0 k‖ ≤ ‖p 0‖ := norm_le_pi_norm (p 0) k
        have h_proj0 : ‖p 0‖ ≤ ‖p‖ := norm_le_pi_norm p 0
        exact h_proj.trans h_proj0
      exact h1.trans_lt hp_norm
    have h_cancel := exp_sub_one_mul_sincFactor (p 0 k) hpk
    calc (p 0 k : ℂ) * hadamardTerm (minkowskiFourier g) k p
      _ = ((Complex.exp (- (Complex.I * ((p 0 k : ℝ) : ℂ))) - 1) * sincFactor (p 0 k)) *
          hadamardTerm (minkowskiFourier g) k p := by rw [h_cancel]
      _ = (Complex.exp (- (Complex.I * ((p 0 k : ℝ) : ℂ))) - 1) *
          (sincFactor (p 0 k) * hadamardTerm (minkowskiFourier g) k p) := by ring

lemma W_one_vanish_of_integral_zero (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (hspec : SpectrumCondition W) (hP : PoincareCovariant R W) (α : Fin 1 → ι)
    (g : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) (hg : ∫ x, g x = 0) :
    W 1 α g = 0 := by
  obtain ⟨m, h, a, h', h_shift, hfg⟩ := W_one_exists_shift_rep g hg
  exact W_one_vanish_of_fourier_sum_shift R W hspec hP α g h a h' h_shift hfg

lemma W_one_eq_integral (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (hspec : SpectrumCondition W) (hP : PoincareCovariant R W) (α : Fin 1 → ι)
    (f : SchwartzMap (Fin 1 → Fin 4 → ℝ) ℂ) :
    W 1 α f = vladimirov_H W 1 α 0 * ∫ x, f x := by
  apply W_one_eq_integral_of_zero_integral R W hspec hP α
  intro g hg
  exact W_one_vanish_of_integral_zero R W hspec hP α g hg

lemma n0_integral (f : SchwartzMap (Fin 0 → Fin 4 → ℝ) ℂ) :
    ∫ x : Fin 0 → Fin 4 → ℝ, f x = f 0 := by
  have h_vol : (volume : Measure (Fin 0 → Fin 4 → ℝ)) = Measure.dirac 0 :=
    Measure.volume_pi_eq_dirac 0
  rw [h_vol, integral_dirac]

lemma n0_euclid_integral (H : EuclideanSpace ℝ (Fin 0 × Fin 4) → ℂ) :
    ∫ u : EuclideanSpace ℝ (Fin 0 × Fin 4), H u = H 0 := by
  have h_meas := EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 0 × Fin 4)
  have h_eq : (∫ u : EuclideanSpace ℝ (Fin 0 × Fin 4), H u) =
      ∫ v : (Fin 0 × Fin 4) → ℝ, H ((MeasurableEquiv.toLp 2 (Fin 0 × Fin 4 → ℝ)) v) := by
    rw [← MeasurePreserving.integral_comp' h_meas]
    rfl
  rw [h_eq]
  have h_pi_vol : (volume : Measure ((Fin 0 × Fin 4) → ℝ)) = Measure.dirac 0 :=
    Measure.volume_pi_eq_dirac 0
  rw [h_pi_vol, integral_dirac]
  have : (MeasurableEquiv.toLp 2 (Fin 0 × Fin 4 → ℝ)) 0 = 0 := Subsingleton.elim _ 0
  rw [this]

lemma schwartz_eq_of_apply_zero (f g : SchwartzMap (Fin 0 → Fin 4 → ℝ) ℂ)
    (h : f 0 = g 0) : f = g := by
  ext x
  have hx : x = 0 := Subsingleton.elim x 0
  rw [hx, h]

lemma vladimirov_psi_schwartz_zero_apply (x : Fin 0 → Fin 4 → ℝ) :
    (vladimirov_psi_schwartz 0 1 Real.zero_lt_one 0) x = 1 := by
  have hx : x = 0 := Subsingleton.elim x 0
  rw [hx]
  change vladimirov_psi 0 1 Real.zero_lt_one 0 0 = 1
  dsimp [vladimirov_psi]
  have h_bump : (vladimirovCutoffBump 0 1 Real.zero_lt_one 0 : ℝ) = 1 := by
    apply (vladimirovCutoffBump 0 1 Real.zero_lt_one).one_of_mem_closedBall
    simp only [Metric.mem_closedBall, dist_self]
    exact zero_le_one
  rw [h_bump]
  dsimp [vladimirov_kernel]
  simp only [Finset.univ_eq_empty, Finset.sum_empty]
  rw [mul_zero, Complex.exp_zero, mul_one]

lemma invMinkowskiFourierCLM_zero_apply
    (g : SchwartzMap (Fin 0 → Fin 4 → ℝ) ℂ) (x : Fin 0 → Fin 4 → ℝ) :
    (invMinkowskiFourierCLM 0 g) x = g 0 := by
  change ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (minkowskiFlipEquiv 0))
    ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (piSpaceEquiv 0))
      ((SchwartzMap.fourierTransformCLM ℂ)
        ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (piSpaceEquiv 0).symm) g)))) x = g 0
  rw [SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
  dsimp only [Function.comp_apply]
  rw [SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
  dsimp only [Function.comp_apply]
  rw [SchwartzMap.fourierTransformCLM_apply]
  rw [SchwartzMap.fourier_coe]
  rw [Real.fourier_eq]
  have h_pt : (piSpaceEquiv 0) (minkowskiFlipEquiv 0 x) = 0 := Subsingleton.elim _ 0
  rw [h_pt]
  rw [n0_euclid_integral]
  have h_c : (Real.fourierChar (- inner ℝ (0 : EuclideanSpace ℝ (Fin 0 × Fin 4)) 0)) = 1 := by
    simp
  rw [h_c, one_smul]
  rw [SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
  dsimp only [Function.comp_apply]
  congr 1

lemma e0_zero_apply (x : Fin 0 → Fin 4 → ℝ) :
    (invMinkowskiFourierCLM 0 (vladimirov_psi_schwartz 0 1 Real.zero_lt_one 0)) x = 1 := by
  rw [invMinkowskiFourierCLM_zero_apply, vladimirov_psi_schwartz_zero_apply]

lemma schwartz_n0_eq_smul_e0 (f : SchwartzMap (Fin 0 → Fin 4 → ℝ) ℂ) :
    f = (f 0) • (invMinkowskiFourierCLM 0 (vladimirov_psi_schwartz 0 1 Real.zero_lt_one 0)) := by
  apply schwartz_eq_of_apply_zero
  have h_apply : ((f 0) • (invMinkowskiFourierCLM 0
      (vladimirov_psi_schwartz 0 1 Real.zero_lt_one 0))) 0 =
      f 0 * (invMinkowskiFourierCLM 0 (vladimirov_psi_schwartz 0 1 Real.zero_lt_one 0)) 0 := rfl
  rw [h_apply, e0_zero_apply 0, mul_one]

omit [Fintype ι] [DecidableEq ι] in
lemma W_zero_eq_integral (W : WightmanFamily ι) (α : Fin 0 → ι)
    (f : SchwartzMap (Fin 0 → Fin 4 → ℝ) ℂ) :
    W 0 α f = vladimirov_H W 0 α 0 * ∫ x, f x := by
  dsimp [vladimirov_H, vladimirov_H_cutoff]
  have h_f : f = (f 0) • (invMinkowskiFourierCLM 0
      (vladimirov_psi_schwartz 0 1 Real.zero_lt_one 0)) :=
    schwartz_n0_eq_smul_e0 f
  nth_rw 1 [h_f]
  rw [map_smul (W 0 α), smul_eq_mul]
  rw [n0_integral f]
  ring

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_H_boundary_zero (W : WightmanFamily ι) (α : Fin 0 → ι)
    (f : SchwartzMap (Fin 0 → Fin 4 → ℝ) ℂ) (v : Fin 4 → ℝ)
    (_hv : v ∈ (forward_light_cone : Set (Fin 4 → ℝ))) :
    Tendsto (fun t : ℝ => ∫ x : Fin 0 → Fin 4 → ℝ,
        vladimirov_H W 0 α
          (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ)) * f x)
      (𝓝[>] (0:ℝ)) (𝓝 (W 0 α f)) := by
  have h_eq : (fun t : ℝ => ∫ x : Fin 0 → Fin 4 → ℝ,
      vladimirov_H W 0 α
        (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ)) * f x) =
      (fun _ => W 0 α f) := by
    ext t
    have h_int : (fun x : Fin 0 → Fin 4 → ℝ =>
        vladimirov_H W 0 α
          (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ)) * f x) =
        (fun x => vladimirov_H W 0 α 0 * f x) := by
      ext x
      have hx : (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ)) = 0 :=
        Subsingleton.elim _ 0
      rw [hx]
    rw [h_int, integral_const_mul]
    rw [W_zero_eq_integral]
  rw [h_eq]
  exact tendsto_const_nhds

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_psi_schwartz_family_analyticAt_zero (R : ℝ) (hR : 0 < R)
    (z : Fin 0 → Fin 4 → ℂ) :
    SchwartzFamilyAnalyticAt 0 R hR z := by
  intro T
  have h_const : ∀ w1 w2 : Fin 0 → Fin 4 → ℂ,
      T (vladimirov_psi_schwartz 0 R hR w1) = T (vladimirov_psi_schwartz 0 R hR w2) := by
    intro w1 w2
    have h_eq : w1 = w2 := Subsingleton.elim w1 w2
    rw [h_eq]
  have h_fun : (fun w => T (vladimirov_psi_schwartz 0 R hR w)) =
      fun _ => T (vladimirov_psi_schwartz 0 R hR 0) := by
    ext w
    exact h_const w 0
  rw [h_fun]
  exact analyticAt_const

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_deriv_psi_add (n : ℕ) (R : ℝ) (hR : 0 < R) (z : Fin n → Fin 4 → ℂ)
    (h1 h2 : Fin n → Fin 4 → ℂ) :
    vladimirov_deriv_psi_schwartz n R hR z (h1 + h2) =
    vladimirov_deriv_psi_schwartz n R hR z h1 +
    vladimirov_deriv_psi_schwartz n R hR z h2 := by
  ext p
  exact vladimirov_deriv_psi_add_eval n R hR z h1 h2 p

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_deriv_psi_smul (n : ℕ) (R : ℝ) (hR : 0 < R) (z : Fin n → Fin 4 → ℂ)
    (c : ℂ) (h : Fin n → Fin 4 → ℂ) :
    vladimirov_deriv_psi_schwartz n R hR z (c • h) =
    c • vladimirov_deriv_psi_schwartz n R hR z h := by
  ext p
  exact vladimirov_deriv_psi_smul_eval n R hR z c h p

omit [Fintype ι] [DecidableEq ι] in
noncomputable def vladimirov_deriv_T_CLM (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z : Fin n → Fin 4 → ℂ) (T : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ →L[ℂ] ℂ) :
    (Fin n → Fin 4 → ℂ) →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun h => T (vladimirov_deriv_psi_schwartz n R hR z h)
      map_add' := by
        intro h1 h2
        rw [vladimirov_deriv_psi_add n R hR z h1 h2]
        exact map_add T _ _
      map_smul' := by
        intro c h
        rw [vladimirov_deriv_psi_smul n R hR z c h]
        exact map_smul T c _ }

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_deriv_T_CLM_apply (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z : Fin n → Fin 4 → ℂ) (T : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ →L[ℂ] ℂ)
    (h : Fin n → Fin 4 → ℂ) :
    (vladimirov_deriv_T_CLM n R hR z T) h =
    T (vladimirov_deriv_psi_schwartz n R hR z h) := rfl

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_fderiv_remainder_linear (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z : Fin n → Fin 4 → ℂ) (T : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ →L[ℂ] ℂ)
    (w : Fin n → Fin 4 → ℂ) :
    T (vladimirov_psi_schwartz n R hR w) - T (vladimirov_psi_schwartz n R hR z) -
      (vladimirov_deriv_T_CLM n R hR z T) (w - z) =
    T (vladimirov_psi_schwartz n R hR w - vladimirov_psi_schwartz n R hR z -
       vladimirov_deriv_psi_schwartz n R hR z (w - z)) := by
  rw [vladimirov_deriv_T_CLM_apply]
  rw [← map_sub, ← map_sub]

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_psi_taylor_eval (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z w : Fin n → Fin 4 → ℂ) (p : Fin n → Fin 4 → ℝ) :
    (vladimirov_psi_schwartz n R hR w - vladimirov_psi_schwartz n R hR z -
     vladimirov_deriv_psi_schwartz n R hR z (w - z)) p =
    vladimirov_psi n R hR z p *
      (Complex.exp (vladimirov_phase_CLM n (w - z) p) - 1 - vladimirov_phase_CLM n (w - z) p) := by
  change (vladimirov_psi n R hR w p) - (vladimirov_psi n R hR z p) -
    (vladimirov_phase_CLM n (w - z) p * vladimirov_psi n R hR z p) = _
  dsimp [vladimirov_psi]
  have h_ker_w : vladimirov_kernel n w p =
      vladimirov_kernel n z p * Complex.exp (vladimirov_phase_CLM n (w - z) p) := by
    change Complex.exp (vladimirov_phase_CLM n w p) =
      Complex.exp (vladimirov_phase_CLM n z p) * Complex.exp (vladimirov_phase_CLM n (w - z) p)
    rw [← Complex.exp_add]
    congr 1
    rw [vladimirov_phase_clm_eq_phase_z_clm n w,
        vladimirov_phase_clm_eq_phase_z_clm n z,
        vladimirov_phase_clm_eq_phase_z_clm n (w - z)]
    rw [← map_add]
    congr 1
    ext i μ
    dsimp
    ring
  rw [h_ker_w]
  ring

omit [Fintype ι] [DecidableEq ι] in
lemma clm_isLittleO_of_norm_le {α E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (T : E →L[ℂ] F) (g : α → E) (f : α → ℂ) (l : Filter α)
    (h_o : g =o[l] f) :
    (fun x => T (g x)) =o[l] f := by
  have h_O : (fun x => T (g x)) =O[l] g := ContinuousLinearMap.isBigO_comp T g l
  exact h_O.trans_isLittleO h_o

omit [Fintype ι] [DecidableEq ι] in
lemma isLittleO_of_pow_two {α : Type*} [NormedAddCommGroup α] (z : α)
    (f : α → ℂ) (C : ℝ)
    (h_bound : ∀ᶠ x in 𝓝 z, ‖f x‖ ≤ C * ‖x - z‖ ^ 2) :
    f =o[𝓝 z] fun x => x - z := by
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  have h_cont : Continuous (fun x : α => C * ‖x - z‖) :=
    continuous_const.mul (continuous_id.sub continuous_const).norm
  have h_lim := h_cont.tendsto z
  simp only [sub_self, norm_zero, mul_zero] at h_lim
  have h_event : ∀ᶠ x in 𝓝 z, C * ‖x - z‖ < c := h_lim.eventually (gt_mem_nhds hc)
  filter_upwards [h_bound, h_event] with x hx h_lt
  calc ‖f x‖ ≤ C * ‖x - z‖ ^ 2 := hx
    _ = (C * ‖x - z‖) * ‖x - z‖ := by ring
    _ ≤ c * ‖x - z‖ := by
      nlinarith [norm_nonneg (x - z)]

omit [Fintype ι] [DecidableEq ι] in
lemma exp_sub_one_sub_id_bound (u : ℂ) (hu : ‖u‖ ≤ 1) :
    ‖Complex.exp u - 1 - u‖ ≤ ‖u‖ ^ 2 :=
  Complex.norm_exp_sub_one_sub_id_le hu

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_phase_bound (n : ℕ) (h : Fin n → Fin 4 → ℂ) (p : Fin n → Fin 4 → ℝ) :
    ‖vladimirov_phase_CLM n h p‖ ≤ ‖vladimirov_phase_z_CLM n p‖ * ‖h‖ := by
  rw [vladimirov_phase_clm_eq_phase_z_clm]
  exact ContinuousLinearMap.le_opNorm (vladimirov_phase_z_CLM n p) h

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_psi_taylor_pointwise_norm_le (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z x' : Fin n → Fin 4 → ℂ) (p : Fin n → Fin 4 → ℝ)
    (hu : ‖vladimirov_phase_CLM n (x' - z) p‖ ≤ 1) :
    ‖(vladimirov_psi_schwartz n R hR x' -
       vladimirov_psi_schwartz n R hR z -
       vladimirov_deriv_psi_schwartz n R hR z (x' - z)) p‖ ≤
    ‖vladimirov_psi n R hR z p‖ * ‖vladimirov_phase_z_CLM n p‖ ^ 2 * ‖x' - z‖ ^ 2 := by
  rw [vladimirov_psi_taylor_eval]
  rw [norm_mul]
  have h_exp := exp_sub_one_sub_id_bound (vladimirov_phase_CLM n (x' - z) p) hu
  have h_phase := vladimirov_phase_bound n (x' - z) p
  have h_sq : ‖vladimirov_phase_CLM n (x' - z) p‖ ^ 2 ≤
      (‖vladimirov_phase_z_CLM n p‖ * ‖x' - z‖) ^ 2 := by
    nlinarith [norm_nonneg (vladimirov_phase_CLM n (x' - z) p),
               norm_nonneg (vladimirov_phase_z_CLM n p),
               norm_nonneg (x' - z)]
  rw [mul_pow] at h_sq
  calc ‖vladimirov_psi n R hR z p‖ *
        ‖Complex.exp (vladimirov_phase_CLM n (x' - z) p) - 1 - vladimirov_phase_CLM n (x' - z) p‖
      ≤ ‖vladimirov_psi n R hR z p‖ * ‖vladimirov_phase_CLM n (x' - z) p‖ ^ 2 := by
        gcongr
    _ ≤ ‖vladimirov_psi n R hR z p‖ * (‖vladimirov_phase_z_CLM n p‖ ^ 2 * ‖x' - z‖ ^ 2) := by
        gcongr
    _ = ‖vladimirov_psi n R hR z p‖ * ‖vladimirov_phase_z_CLM n p‖ ^ 2 * ‖x' - z‖ ^ 2 := by
        ring

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_psi_eq_zero_of_not_mem_support (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z : Fin n → Fin 4 → ℂ) (p : Fin n → Fin 4 → ℝ)
    (hp : p ∉ Function.support (vladimirovCutoffBump n R hR)) :
    vladimirov_psi n R hR z p = 0 := by
  dsimp [vladimirov_psi]
  rw [Function.mem_support, Classical.not_not] at hp
  rw [hp]
  simp

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_psi_taylor_zero_of_not_mem_support (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z x' : Fin n → Fin 4 → ℂ) (p : Fin n → Fin 4 → ℝ)
    (hp : p ∉ Function.support (vladimirovCutoffBump n R hR)) :
    (vladimirov_psi_schwartz n R hR x' -
     vladimirov_psi_schwartz n R hR z -
     vladimirov_deriv_psi_schwartz n R hR z (x' - z)) p = 0 := by
  rw [vladimirov_psi_taylor_eval]
  rw [vladimirov_psi_eq_zero_of_not_mem_support n R hR z p hp]
  simp

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_phase_le_one_of_dist_le (n : ℕ) (h : Fin n → Fin 4 → ℂ) (p : Fin n → Fin 4 → ℝ)
    (h_dist : ‖h‖ ≤ (‖vladimirov_phase_z_CLM n p‖ + 1)⁻¹) :
    ‖vladimirov_phase_CLM n h p‖ ≤ 1 := by
  have h_bound := vladimirov_phase_bound n h p
  have h_pos : 0 < ‖vladimirov_phase_z_CLM n p‖ + 1 := by
    linarith [norm_nonneg (vladimirov_phase_z_CLM n p)]
  have h_le : ‖vladimirov_phase_z_CLM n p‖ * ‖h‖ ≤ 1 := by
    calc ‖vladimirov_phase_z_CLM n p‖ * ‖h‖
        ≤ ‖vladimirov_phase_z_CLM n p‖ * (‖vladimirov_phase_z_CLM n p‖ + 1)⁻¹ := by
          gcongr
      _ ≤ (‖vladimirov_phase_z_CLM n p‖ + 1) * (‖vladimirov_phase_z_CLM n p‖ + 1)⁻¹ := by
          gcongr
          linarith
      _ = 1 := mul_inv_cancel₀ (ne_of_gt h_pos)
  linarith

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_psi_taylor_pointwise_bound_of_dist_le (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z x' : Fin n → Fin 4 → ℂ) (p : Fin n → Fin 4 → ℝ)
    (h_dist : ‖x' - z‖ ≤ (‖vladimirov_phase_z_CLM n p‖ + 1)⁻¹) :
    ‖(vladimirov_psi_schwartz n R hR x' -
       vladimirov_psi_schwartz n R hR z -
       vladimirov_deriv_psi_schwartz n R hR z (x' - z)) p‖ ≤
    ‖vladimirov_psi n R hR z p‖ * ‖vladimirov_phase_z_CLM n p‖ ^ 2 * ‖x' - z‖ ^ 2 := by
  have hu := vladimirov_phase_le_one_of_dist_le n (x' - z) p h_dist
  exact vladimirov_psi_taylor_pointwise_norm_le n R hR z x' p hu

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_deriv_psi_zero (n : ℕ) (R : ℝ) (hR : 0 < R) (z : Fin n → Fin 4 → ℂ) :
    vladimirov_deriv_psi_schwartz n R hR z 0 = 0 := by
  have h0 : (0 : Fin n → Fin 4 → ℂ) = (0 : ℂ) • 0 := by simp
  rw [h0, vladimirov_deriv_psi_smul, zero_smul]

omit [Fintype ι] [DecidableEq ι] in
noncomputable def vladimirov_remainder_ratio (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z : Fin n → Fin 4 → ℂ) (T : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ →L[ℂ] ℂ)
    (x' : Fin n → Fin 4 → ℂ) : ℝ :=
  if x' = z then 0 else
    ‖T (vladimirov_psi_schwartz n R hR x' -
        vladimirov_psi_schwartz n R hR z -
        vladimirov_deriv_psi_schwartz n R hR z (x' - z))‖ / ‖x' - z‖ ^ 2

omit [Fintype ι] [DecidableEq ι] in
lemma norm_le_ratio_mul_sq (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z : Fin n → Fin 4 → ℂ) (T : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ →L[ℂ] ℂ)
    (x' : Fin n → Fin 4 → ℂ) :
    ‖T (vladimirov_psi_schwartz n R hR x' -
        vladimirov_psi_schwartz n R hR z -
        vladimirov_deriv_psi_schwartz n R hR z (x' - z))‖ ≤
    (vladimirov_remainder_ratio n R hR z T x') * ‖x' - z‖ ^ 2 := by
  dsimp [vladimirov_remainder_ratio]
  split_ifs with h_eq
  · subst h_eq
    rw [sub_self, sub_self, vladimirov_deriv_psi_zero, sub_zero, map_zero, norm_zero]
    simp
  · rw [div_mul_cancel₀]
    have h_ne : ‖x' - z‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr h_eq)
    exact pow_ne_zero 2 h_ne

omit [Fintype ι] [DecidableEq ι] in
lemma schwartz_clm_bound (n : ℕ) (T : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ →L[ℂ] ℂ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧ ∀ f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ,
      ‖T f‖ ≤ C * (s.sup (schwartzSeminormFamily ℝ (Fin n → Fin 4 → ℝ) ℂ)) f := by
  have h_with : WithSeminorms (schwartzSeminormFamily ℝ (Fin n → Fin 4 → ℝ) ℂ) :=
    schwartz_withSeminorms ℝ _ _
  let T_real : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ →ₗ[ℝ] ℂ :=
    T.toLinearMap.restrictScalars ℝ
  let q : Seminorm ℝ (SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :=
    (normSeminorm ℝ ℂ).comp T_real
  have hq_cont : Continuous q := by
    change Continuous (fun f => ‖T f‖)
    exact continuous_norm.comp T.continuous
  obtain ⟨s, C, hC_ne, hq_le⟩ := Seminorm.bound_of_continuous h_with q hq_cont
  refine ⟨s, C, ?_, ?_⟩
  · have hC_ne' : (C : ℝ) ≠ 0 := by exact_mod_cast hC_ne
    exact lt_of_le_of_ne (NNReal.coe_nonneg C) hC_ne'.symm
  · intro f
    have h_eval := hq_le f
    exact h_eval

omit [Fintype ι] [DecidableEq ι] in
noncomputable def schwartz_single_seminorm_ratio (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z : Fin n → Fin 4 → ℂ) (km : ℕ × ℕ) (x' : Fin n → Fin 4 → ℂ) : ℝ :=
  if x' = z then 0 else
    (schwartzSeminormFamily ℝ (Fin n → Fin 4 → ℝ) ℂ km)
      (vladimirov_psi_schwartz n R hR x' -
       vladimirov_psi_schwartz n R hR z -
       vladimirov_deriv_psi_schwartz n R hR z (x' - z)) / ‖x' - z‖ ^ 2

omit [Fintype ι] [DecidableEq ι] in
lemma seminorm_le_single_ratio_mul_sq (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z : Fin n → Fin 4 → ℂ) (km : ℕ × ℕ) (x' : Fin n → Fin 4 → ℂ) :
    (schwartzSeminormFamily ℝ (Fin n → Fin 4 → ℝ) ℂ km)
      (vladimirov_psi_schwartz n R hR x' -
       vladimirov_psi_schwartz n R hR z -
       vladimirov_deriv_psi_schwartz n R hR z (x' - z)) ≤
    (schwartz_single_seminorm_ratio n R hR z km x') * ‖x' - z‖ ^ 2 := by
  dsimp [schwartz_single_seminorm_ratio]
  split_ifs with h_eq
  · subst h_eq
    rw [sub_self, sub_self, vladimirov_deriv_psi_zero, sub_zero, map_zero]
    simp
  · rw [div_mul_cancel₀]
    have h_ne : ‖x' - z‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr h_eq)
    exact pow_ne_zero 2 h_ne

omit [Fintype ι] [DecidableEq ι] in
lemma schwartz_single_seminorm_ratio_le_iff (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z x' : Fin (n + 1) → Fin 4 → ℂ) (km : ℕ × ℕ) (C : ℝ) (hC : 0 ≤ C) :
    schwartz_single_seminorm_ratio (n + 1) R hR z km x' ≤ C ↔
    (schwartzSeminormFamily ℝ (Fin (n + 1) → Fin 4 → ℝ) ℂ km)
      (vladimirov_psi_schwartz (n + 1) R hR x' -
       vladimirov_psi_schwartz (n + 1) R hR z -
       vladimirov_deriv_psi_schwartz (n + 1) R hR z (x' - z)) ≤ C * ‖x' - z‖ ^ 2 := by
  dsimp [schwartz_single_seminorm_ratio]
  split_ifs with h_eq
  · subst h_eq
    simp only [sub_self, vladimirov_deriv_psi_zero, map_zero, norm_zero, ne_eq,
      OfNat.ofNat_ne_zero, not_false_iff, zero_pow, mul_zero, le_rfl]
    simp [hC]
  · have h_pos : 0 < ‖x' - z‖ ^ 2 := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr (sub_ne_zero.mpr h_eq))
    rw [div_le_iff₀ h_pos]

omit [Fintype ι] [DecidableEq ι] in
lemma seminorm_zero_le_of_pointwise_bound (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z x' : Fin n → Fin 4 → ℂ) (k : ℕ) (M : ℝ) (hM_nonneg : 0 ≤ M)
    (hM : ∀ p, ‖p‖ ^ k * ‖(vladimirov_psi_schwartz n R hR x' -
         vladimirov_psi_schwartz n R hR z -
         vladimirov_deriv_psi_schwartz n R hR z (x' - z)) p‖ ≤ M) :
    (SchwartzMap.seminorm ℝ k 0)
        (vladimirov_psi_schwartz n R hR x' -
         vladimirov_psi_schwartz n R hR z -
         vladimirov_deriv_psi_schwartz n R hR z (x' - z)) ≤ M := by
  refine SchwartzMap.seminorm_le_bound ℝ k 0 _ hM_nonneg ?_
  intro p
  simpa only [norm_iteratedFDeriv_zero] using hM p

omit [Fintype ι] [DecidableEq ι] in
lemma seminorm_succ_le_of_pointwise_bound (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z x' : Fin n → Fin 4 → ℂ) (k m : ℕ) (M : ℝ) (hM_nonneg : 0 ≤ M)
    (hM : ∀ p, ‖p‖ ^ k * ‖iteratedFDeriv ℝ (m + 1)
         (⇑(vladimirov_psi_schwartz n R hR x' -
            vladimirov_psi_schwartz n R hR z -
            vladimirov_deriv_psi_schwartz n R hR z (x' - z))) p‖ ≤ M) :
    (SchwartzMap.seminorm ℝ k (m + 1))
        (vladimirov_psi_schwartz n R hR x' -
         vladimirov_psi_schwartz n R hR z -
         vladimirov_deriv_psi_schwartz n R hR z (x' - z)) ≤ M := by
  refine SchwartzMap.seminorm_le_bound ℝ k (m + 1) _ hM_nonneg (fun p => hM p)

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_support_norm_lt (n : ℕ) (R : ℝ) (hR : 0 < R)
    (p : Fin (n + 1) → Fin 4 → ℝ)
    (hp : p ∈ Function.support (vladimirovCutoffBump (n + 1) R hR)) :
    ‖p‖ < 2 * R := by
  have h_supp := (vladimirovCutoffBump (n + 1) R hR).support_eq
  rw [h_supp, Metric.mem_ball, dist_zero_right] at hp
  exact hp

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_pi_bound (n : ℕ) (p : Fin (n + 1) → Fin 4 → ℝ) (k : Fin (n + 1)) (μ : Fin 4) :
    |p k μ| ≤ ‖p‖ := by
  have h1 : |p k μ| = ‖p k μ‖ := Real.norm_eq_abs (p k μ) ▸ rfl
  rw [h1]
  have h2 : ‖p k μ‖ ≤ ‖p k‖ := norm_le_pi_norm (p k) μ
  have h3 : ‖p k‖ ≤ ‖p‖ := norm_le_pi_norm p k
  exact h2.trans h3

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_pi_bound_c (n : ℕ) (z : Fin (n + 1) → Fin 4 → ℂ) (k : Fin (n + 1)) (μ : Fin 4) :
    ‖z k μ‖ ≤ ‖z‖ := by
  have h2 : ‖z k μ‖ ≤ ‖z k‖ := norm_le_pi_norm (z k) μ
  have h3 : ‖z k‖ ≤ ‖z‖ := norm_le_pi_norm z k
  exact h2.trans h3

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_term_bound (n : ℕ) (p : Fin (n + 1) → Fin 4 → ℝ) (z : Fin (n + 1) → Fin 4 → ℂ)
    (k : Fin (n + 1)) (μ : Fin 4) :
    ‖(p k μ : ℂ) * z k μ‖ ≤ ‖p‖ * ‖z‖ := by
  rw [norm_mul, Complex.norm_real]
  exact mul_le_mul (vladimirov_pi_bound n p k μ) (vladimirov_pi_bound_c n z k μ)
    (norm_nonneg _) (norm_nonneg _)

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_inner_bound (n : ℕ) (p : Fin (n + 1) → Fin 4 → ℝ) (z : Fin (n + 1) → Fin 4 → ℂ)
    (k : Fin (n + 1)) :
    ‖minkowskiInnerC (fun μ => (p k μ : ℂ)) (z k)‖ ≤ 4 * (‖p‖ * ‖z‖) := by
  dsimp [minkowskiInnerC]
  have h0 := vladimirov_term_bound n p z k 0
  have h1 := vladimirov_term_bound n p z k 1
  have h2 := vladimirov_term_bound n p z k 2
  have h3 := vladimirov_term_bound n p z k 3
  have s1 : ‖(p k 0 : ℂ) * z k 0 - (p k 1 : ℂ) * z k 1 - (p k 2 : ℂ) * z k 2 - (p k 3 : ℂ) * z k 3‖
      ≤ ‖(p k 0 : ℂ) * z k 0 - (p k 1 : ℂ) * z k 1 - (p k 2 : ℂ) * z k 2‖ + ‖(p k 3 : ℂ) * z k 3‖ :=
    norm_sub_le _ _
  have s2 : ‖(p k 0 : ℂ) * z k 0 - (p k 1 : ℂ) * z k 1 - (p k 2 : ℂ) * z k 2‖
      ≤ ‖(p k 0 : ℂ) * z k 0 - (p k 1 : ℂ) * z k 1‖ + ‖(p k 2 : ℂ) * z k 2‖ :=
    norm_sub_le _ _
  have s3 : ‖(p k 0 : ℂ) * z k 0 - (p k 1 : ℂ) * z k 1‖
      ≤ ‖(p k 0 : ℂ) * z k 0‖ + ‖(p k 1 : ℂ) * z k 1‖ :=
    norm_sub_le _ _
  linarith

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_phase_z_clm_linear_bound (n : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ p : Fin (n + 1) → Fin 4 → ℝ,
      ‖vladimirov_phase_z_CLM (n + 1) p‖ ≤ M * ‖p‖ := by
  use 4 * ((n : ℝ) + 1)
  refine ⟨by positivity, ?_⟩
  intro p
  have h_bound : ∀ z : Fin (n + 1) → Fin 4 → ℂ,
      ‖(vladimirov_phase_z_CLM (n + 1) p) z‖ ≤ (4 * ((n : ℝ) + 1) * ‖p‖) * ‖z‖ := by
    intro z
    have h_eval : (vladimirov_phase_z_CLM (n + 1) p) z =
        - Complex.I * (∑ k : Fin (n + 1), minkowskiInnerC (fun μ => (p k μ : ℂ)) (z k)) := rfl
    rw [h_eval, norm_mul, norm_neg, Complex.norm_I, one_mul]
    have h_sum_le : ‖∑ k : Fin (n + 1), minkowskiInnerC (fun μ => (p k μ : ℂ)) (z k)‖ ≤
        ∑ k : Fin (n + 1), ‖minkowskiInnerC (fun μ => (p k μ : ℂ)) (z k)‖ :=
      norm_sum_le _ _
    have h_each_le : ∑ k : Fin (n + 1), ‖minkowskiInnerC (fun μ => (p k μ : ℂ)) (z k)‖ ≤
        ∑ k : Fin (n + 1), 4 * (‖p‖ * ‖z‖) :=
      Finset.sum_le_sum (fun k _ => vladimirov_inner_bound n p z k)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h_each_le
    push_cast at h_each_le
    have h_comb : ‖∑ k : Fin (n + 1), minkowskiInnerC (fun μ => (p k μ : ℂ)) (z k)‖ ≤
        ((n : ℝ) + 1) * (4 * (‖p‖ * ‖z‖)) :=
      h_sum_le.trans h_each_le
    calc ‖∑ k : Fin (n + 1), minkowskiInnerC (fun μ => (p k μ : ℂ)) (z k)‖
        ≤ ((n : ℝ) + 1) * (4 * (‖p‖ * ‖z‖)) := h_comb
      _ = (4 * ((n : ℝ) + 1) * ‖p‖) * ‖z‖ := by ring
  have h_pos : 0 ≤ 4 * ((n : ℝ) + 1) * ‖p‖ := by positivity
  exact ContinuousLinearMap.opNorm_le_bound (vladimirov_phase_z_CLM (n + 1) p) h_pos h_bound

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_phase_z_clm_support_bound (n : ℕ) (R : ℝ) (hR : 0 < R) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p ∈ Function.support (vladimirovCutoffBump (n + 1) R hR),
      ‖vladimirov_phase_z_CLM (n + 1) p‖ ≤ B := by
  obtain ⟨M, hM_nonneg, hM⟩ := vladimirov_phase_z_clm_linear_bound n
  use M * (2 * R)
  refine ⟨by positivity, ?_⟩
  intro p hp
  have hp_lt := vladimirov_support_norm_lt n R hR p hp
  have hp_le : ‖p‖ ≤ 2 * R := hp_lt.le
  have h_bound := hM p
  calc ‖vladimirov_phase_z_CLM (n + 1) p‖
      ≤ M * ‖p‖ := h_bound
    _ ≤ M * (2 * R) := by gcongr

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_phase_z_clm_ball_bound (n : ℕ) (R : ℝ) (hR : 0 < R) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p, ‖p‖ ≤ 2 * R →
      ‖vladimirov_phase_z_CLM (n + 1) p‖ ≤ B := by
  obtain ⟨M, hM_nonneg, hM⟩ := vladimirov_phase_z_clm_linear_bound n
  use M * (2 * R)
  refine ⟨by positivity, ?_⟩
  intro p hp
  have h_bound := hM p
  calc ‖vladimirov_phase_z_CLM (n + 1) p‖
      ≤ M * ‖p‖ := h_bound
    _ ≤ M * (2 * R) := by gcongr

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_phase_dist_bound_exists (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z : Fin (n + 1) → Fin 4 → ℂ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (x' : Fin (n + 1) → Fin 4 → ℂ), ‖x' - z‖ ≤ δ →
      ∀ p ∈ Function.support (vladimirovCutoffBump (n + 1) R hR),
        ‖x' - z‖ ≤ (‖vladimirov_phase_z_CLM (n + 1) p‖ + 1)⁻¹ := by
  obtain ⟨B, hB_nonneg, hB⟩ := vladimirov_phase_z_clm_support_bound n R hR
  have hB_pos : 0 < B + 1 := by linarith
  use (B + 1)⁻¹
  refine ⟨inv_pos.mpr hB_pos, ?_⟩
  intro x' hx' p hp
  have h_le := hB p hp
  have h_add_le : ‖vladimirov_phase_z_CLM (n + 1) p‖ + 1 ≤ B + 1 := by linarith
  have h_pos_p : 0 < ‖vladimirov_phase_z_CLM (n + 1) p‖ + 1 := by
    linarith [norm_nonneg (vladimirov_phase_z_CLM (n + 1) p)]
  have h_inv_le : (B + 1)⁻¹ ≤ (‖vladimirov_phase_z_CLM (n + 1) p‖ + 1)⁻¹ :=
    (inv_le_inv₀ hB_pos h_pos_p).mpr h_add_le
  exact hx'.trans h_inv_le

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_norm_exp_le (w : ℂ) : ‖Complex.exp w‖ ≤ Real.exp ‖w‖ := by
  rw [Complex.norm_exp]
  have h : w.re ≤ ‖w‖ := Complex.re_le_norm w
  exact Real.exp_le_exp.mpr h

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_bump_norm_le (n : ℕ) (R : ℝ) (hR : 0 < R) (p : Fin (n + 1) → Fin 4 → ℝ) :
    ‖((vladimirovCutoffBump (n + 1) R hR p : ℝ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  have h_nonneg : 0 ≤ (vladimirovCutoffBump (n + 1) R hR : (Fin (n + 1) → Fin 4 → ℝ) → ℝ) p :=
    (vladimirovCutoffBump (n + 1) R hR).nonneg
  have h_le : (vladimirovCutoffBump (n + 1) R hR : (Fin (n + 1) → Fin 4 → ℝ) → ℝ) p ≤ 1 :=
    (vladimirovCutoffBump (n + 1) R hR).le_one
  rw [abs_of_nonneg h_nonneg]
  exact h_le

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_kernel_bound_on_support (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z : Fin (n + 1) → Fin 4 → ℂ) (p : Fin (n + 1) → Fin 4 → ℝ)
    (hp : p ∈ Function.support (vladimirovCutoffBump (n + 1) R hR)) :
    ‖vladimirov_kernel (n + 1) z p‖ ≤ Real.exp (‖vladimirov_phase_CLM (n + 1) z‖ * (2 * R)) := by
  have h_eval : vladimirov_kernel (n + 1) z p =
      Complex.exp ((vladimirov_phase_CLM (n + 1) z) p) := rfl
  rw [h_eval]
  have h_exp := vladimirov_norm_exp_le ((vladimirov_phase_CLM (n + 1) z) p)
  have hp_lt := vladimirov_support_norm_lt n R hR p hp
  have hp_le : ‖p‖ ≤ 2 * R := hp_lt.le
  have h_clm := (vladimirov_phase_CLM (n + 1) z).le_opNorm p
  have h_le : ‖(vladimirov_phase_CLM (n + 1) z) p‖ ≤
      ‖vladimirov_phase_CLM (n + 1) z‖ * (2 * R) := by
    calc ‖(vladimirov_phase_CLM (n + 1) z) p‖
        ≤ ‖vladimirov_phase_CLM (n + 1) z‖ * ‖p‖ := h_clm
      _ ≤ ‖vladimirov_phase_CLM (n + 1) z‖ * (2 * R) := by gcongr
  have h_exp_le : Real.exp ‖(vladimirov_phase_CLM (n + 1) z) p‖ ≤
      Real.exp (‖vladimirov_phase_CLM (n + 1) z‖ * (2 * R)) :=
    Real.exp_le_exp.mpr h_le
  exact h_exp.trans h_exp_le

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_psi_bound_on_support (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z : Fin (n + 1) → Fin 4 → ℂ) (p : Fin (n + 1) → Fin 4 → ℝ)
    (hp : p ∈ Function.support (vladimirovCutoffBump (n + 1) R hR)) :
    ‖vladimirov_psi (n + 1) R hR z p‖ ≤ Real.exp (‖vladimirov_phase_CLM (n + 1) z‖ * (2 * R)) := by
  dsimp [vladimirov_psi]
  rw [norm_mul]
  have h_bump := vladimirov_bump_norm_le n R hR p
  have h_ker := vladimirov_kernel_bound_on_support n R hR z p hp
  calc ‖((vladimirovCutoffBump (n + 1) R hR p : ℝ) : ℂ)‖ * ‖vladimirov_kernel (n + 1) z p‖
      ≤ 1 * ‖vladimirov_kernel (n + 1) z p‖ := by gcongr
    _ = ‖vladimirov_kernel (n + 1) z p‖ := one_mul _
    _ ≤ Real.exp (‖vladimirov_phase_CLM (n + 1) z‖ * (2 * R)) := h_ker

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_psi_taylor_support_bound_exists (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z : Fin (n + 1) → Fin 4 → ℂ) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ Function.support (vladimirovCutoffBump (n + 1) R hR),
      ‖p‖ ^ k * ‖vladimirov_psi (n + 1) R hR z p‖ * ‖vladimirov_phase_z_CLM (n + 1) p‖ ^ 2 ≤ C := by
  obtain ⟨B, hB_nonneg, hB⟩ := vladimirov_phase_z_clm_support_bound n R hR
  let C := (2 * R) ^ k * Real.exp (‖vladimirov_phase_CLM (n + 1) z‖ * (2 * R)) * B ^ 2
  use C
  refine ⟨by positivity, ?_⟩
  intro p hp
  have hp_lt := vladimirov_support_norm_lt n R hR p hp
  have hp_le : ‖p‖ ≤ 2 * R := hp_lt.le
  have h_pk : ‖p‖ ^ k ≤ (2 * R) ^ k := by gcongr
  have h_psi := vladimirov_psi_bound_on_support n R hR z p hp
  have h_phase := hB p hp
  have h_phase2 : ‖vladimirov_phase_z_CLM (n + 1) p‖ ^ 2 ≤ B ^ 2 := by gcongr
  calc ‖p‖ ^ k * ‖vladimirov_psi (n + 1) R hR z p‖ * ‖vladimirov_phase_z_CLM (n + 1) p‖ ^ 2
      ≤ (2 * R) ^ k * Real.exp (‖vladimirov_phase_CLM (n + 1) z‖ * (2 * R)) * B ^ 2 := by gcongr

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_psi_taylor_seminorm_zero_pointwise_bound (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z : Fin (n + 1) → Fin 4 → ℂ) (k : ℕ) :
    ∃ (C : ℝ), 0 ≤ C ∧ ∀ᶠ x' in 𝓝 z,
      ∀ p, ‖p‖ ^ k * ‖(vladimirov_psi_schwartz (n + 1) R hR x' -
                       vladimirov_psi_schwartz (n + 1) R hR z -
                       vladimirov_deriv_psi_schwartz (n + 1) R hR z (x' - z)) p‖ ≤
        C * ‖x' - z‖ ^ 2 := by
  obtain ⟨δ, hδ_pos, hδ⟩ := vladimirov_phase_dist_bound_exists n R hR z
  obtain ⟨C, hC_nonneg, hC⟩ := vladimirov_psi_taylor_support_bound_exists n R hR z k
  use C
  refine ⟨hC_nonneg, ?_⟩
  have h_ball : Metric.closedBall z δ ∈ 𝓝 z := Metric.closedBall_mem_nhds z hδ_pos
  have h_eq : Metric.closedBall z δ = {x' | ‖x' - z‖ ≤ δ} := by
    ext x'
    rw [Metric.mem_closedBall, dist_eq_norm]
    rfl
  have h_nhds : {x' | ‖x' - z‖ ≤ δ} ∈ 𝓝 z := by rwa [← h_eq]
  filter_upwards [h_nhds] with x' hx'
  intro p
  by_cases hp : p ∈ Function.support (vladimirovCutoffBump (n + 1) R hR)
  · have h_dist := hδ x' hx' p hp
    have h_point := vladimirov_psi_taylor_pointwise_bound_of_dist_le (n + 1) R hR z x' p h_dist
    have h_C_p := hC p hp
    calc ‖p‖ ^ k * ‖(vladimirov_psi_schwartz (n + 1) R hR x' -
                     vladimirov_psi_schwartz (n + 1) R hR z -
                     vladimirov_deriv_psi_schwartz (n + 1) R hR z (x' - z)) p‖
        ≤ ‖p‖ ^ k * (‖vladimirov_psi (n + 1) R hR z p‖ *
                     ‖vladimirov_phase_z_CLM (n + 1) p‖ ^ 2 * ‖x' - z‖ ^ 2) := by
          gcongr
      _ = (‖p‖ ^ k * ‖vladimirov_psi (n + 1) R hR z p‖ *
           ‖vladimirov_phase_z_CLM (n + 1) p‖ ^ 2) * ‖x' - z‖ ^ 2 := by ring
      _ ≤ C * ‖x' - z‖ ^ 2 := by
          gcongr
  · have h_zero := vladimirov_psi_taylor_zero_of_not_mem_support (n + 1) R hR z x' p hp
    rw [h_zero, norm_zero, mul_zero]
    positivity

omit [Fintype ι] [DecidableEq ι] in
lemma schwartz_single_seminorm_quadratic_zero_deriv (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z : Fin (n + 1) → Fin 4 → ℂ) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x' in 𝓝 z,
      (SchwartzMap.seminorm ℝ k 0)
        (vladimirov_psi_schwartz (n + 1) R hR x' -
         vladimirov_psi_schwartz (n + 1) R hR z -
         vladimirov_deriv_psi_schwartz (n + 1) R hR z (x' - z)) ≤ C * ‖x' - z‖ ^ 2 := by
  obtain ⟨C, hC_nonneg, hC⟩ := vladimirov_psi_taylor_seminorm_zero_pointwise_bound n R hR z k
  use C
  refine ⟨hC_nonneg, ?_⟩
  filter_upwards [hC] with x' hx'
  have h_bound_nonneg : 0 ≤ C * ‖x' - z‖ ^ 2 := mul_nonneg hC_nonneg (sq_nonneg _)
  exact seminorm_zero_le_of_pointwise_bound (n + 1) R hR z x' k
    (C * ‖x' - z‖ ^ 2) h_bound_nonneg hx'

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_psi_taylor_succ_eventually_zero_of_lt (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z x' : Fin (n + 1) → Fin 4 → ℂ) (p : Fin (n + 1) → Fin 4 → ℝ)
    (hp : 2 * R < ‖p‖) :
    (⇑(vladimirov_psi_schwartz (n + 1) R hR x' -
       vladimirov_psi_schwartz (n + 1) R hR z -
       vladimirov_deriv_psi_schwartz (n + 1) R hR z (x' - z))) =ᶠ[𝓝 p]
      (0 : (Fin (n + 1) → Fin 4 → ℝ) → ℂ) := by
  have h_open : IsOpen {q : Fin (n + 1) → Fin 4 → ℝ | 2 * R < ‖q‖} :=
    isOpen_lt continuous_const continuous_norm
  have h_mem : {q : Fin (n + 1) → Fin 4 → ℝ | 2 * R < ‖q‖} ∈ 𝓝 p :=
    h_open.mem_nhds hp
  filter_upwards [h_mem] with q hq
  have h_not : q ∉ Function.support (vladimirovCutoffBump (n + 1) R hR) := by
    rw [(vladimirovCutoffBump (n + 1) R hR).support_eq, Metric.mem_ball, dist_zero_right]
    exact not_lt.mpr (le_of_lt hq)
  exact vladimirov_psi_taylor_zero_of_not_mem_support (n + 1) R hR z x' q h_not

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_psi_taylor_succ_zero_of_lt (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z x' : Fin (n + 1) → Fin 4 → ℂ) (p : Fin (n + 1) → Fin 4 → ℝ) (m : ℕ)
    (hp : 2 * R < ‖p‖) :
    iteratedFDeriv ℝ (m + 1)
      (⇑(vladimirov_psi_schwartz (n + 1) R hR x' -
         vladimirov_psi_schwartz (n + 1) R hR z -
         vladimirov_deriv_psi_schwartz (n + 1) R hR z (x' - z))) p = 0 := by
  have h_eq := vladimirov_psi_taylor_succ_eventually_zero_of_lt n R hR z x' p hp
  have h_deriv := (Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) h_eq (m + 1)).self_of_nhds
  rw [h_deriv, iteratedFDeriv_zero]
  rfl

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_psi_taylor_funext (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z x' : Fin (n + 1) → Fin 4 → ℂ) :
    ⇑(vladimirov_psi_schwartz (n + 1) R hR x' -
       vladimirov_psi_schwartz (n + 1) R hR z -
       vladimirov_deriv_psi_schwartz (n + 1) R hR z (x' - z)) =
    fun p => vladimirov_psi (n + 1) R hR z p *
      (Complex.exp (vladimirov_phase_CLM (n + 1) (x' - z) p) - 1 -
       vladimirov_phase_CLM (n + 1) (x' - z) p) := by
  ext p
  exact vladimirov_psi_taylor_eval (n + 1) R hR z x' p

omit [Fintype ι] [DecidableEq ι] in
lemma norm_iteratedFDeriv_le_seminorm (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z x' : Fin (n + 1) → Fin 4 → ℂ) (p : Fin (n + 1) → Fin 4 → ℝ) (m : ℕ) :
    ‖iteratedFDeriv ℝ (m + 1)
       (⇑(vladimirov_psi_schwartz (n + 1) R hR x' -
          vladimirov_psi_schwartz (n + 1) R hR z -
          vladimirov_deriv_psi_schwartz (n + 1) R hR z (x' - z))) p‖ ≤
    (SchwartzMap.seminorm ℝ 0 (m + 1))
      (vladimirov_psi_schwartz (n + 1) R hR x' -
       vladimirov_psi_schwartz (n + 1) R hR z -
       vladimirov_deriv_psi_schwartz (n + 1) R hR z (x' - z)) := by
  have h := SchwartzMap.le_seminorm (𝕜 := ℝ) 0 (m + 1)
    (vladimirov_psi_schwartz (n + 1) R hR x' -
     vladimirov_psi_schwartz (n + 1) R hR z -
     vladimirov_deriv_psi_schwartz (n + 1) R hR z (x' - z)) p
  simp only [pow_zero, one_mul] at h
  exact h

omit [Fintype ι] [DecidableEq ι] in
lemma taylor_remainder_two_of_mvt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ϕ : ℝ → E) (ϕ' ϕ'' : ℝ → E) (C2 : ℝ)
    (hϕ' : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt ϕ (ϕ' t) t)
    (hϕ'' : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt ϕ' (ϕ'' t) t)
    (hbound : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖ϕ'' t‖ ≤ C2) :
    ‖ϕ 1 - ϕ 0 - ϕ' 0‖ ≤ C2 := by
  have hC2 : 0 ≤ C2 := (norm_nonneg _).trans (hbound 0 ⟨le_rfl, zero_le_one⟩)
  have hϕ'_diff : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivWithinAt ϕ' (ϕ'' t) (Set.Icc 0 1) t :=
    fun t ht => (hϕ'' t ht).hasDerivWithinAt (s := Set.Icc 0 1)
  have hϕ'_bound : ∀ t ∈ Set.Ico (0 : ℝ) 1, ‖ϕ'' t‖ ≤ C2 :=
    fun t ht => hbound t (Set.Ico_subset_Icc_self ht)
  have h_mvt1 := norm_image_sub_le_of_norm_deriv_le_segment' hϕ'_diff hϕ'_bound
  have hψ : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivWithinAt (fun s => ϕ s - s • ϕ' 0) (ϕ' t - ϕ' 0) (Set.Icc 0 1) t := by
    intro t ht
    have h1 : HasDerivWithinAt ϕ (ϕ' t) (Set.Icc 0 1) t := (hϕ' t ht).hasDerivWithinAt
    have h2 : HasDerivWithinAt (fun s => s • ϕ' 0) (ϕ' 0) (Set.Icc 0 1) t := by
      simpa using ((hasDerivAt_id t).hasDerivWithinAt (s := Set.Icc 0 1)).smul_const (ϕ' 0)
    exact h1.sub h2
  have hψ_bound : ∀ t ∈ Set.Ico (0 : ℝ) 1, ‖ϕ' t - ϕ' 0‖ ≤ C2 := by
    intro t ht
    have ht_icc : t ∈ Set.Icc (0 : ℝ) 1 := Set.Ico_subset_Icc_self ht
    have h_le := h_mvt1 t ht_icc
    rw [sub_zero] at h_le
    calc ‖ϕ' t - ϕ' 0‖ ≤ C2 * t := h_le
      _ ≤ C2 * 1 := by nlinarith [ht.2]
      _ = C2 := mul_one C2
  have h_mvt2 := norm_image_sub_le_of_norm_deriv_le_segment' hψ hψ_bound 1
    (Set.right_mem_Icc.2 zero_le_one)
  simp only [one_smul, zero_smul, sub_zero, mul_one] at h_mvt2
  have h_reorder : ϕ 1 - ϕ 0 - ϕ' 0 = ϕ 1 - ϕ' 0 - ϕ 0 := by abel
  rw [h_reorder]
  exact h_mvt2

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_psi_taylor_succ_compact_pointwise_bound_eq (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z : Fin (n + 1) → Fin 4 → ℂ) (p : Fin (n + 1) → Fin 4 → ℝ) (m : ℕ)
    (M : ℝ) (_hM_nonneg : 0 ≤ M) :
    ‖iteratedFDeriv ℝ (m + 1)
       (⇑(vladimirov_psi_schwartz (n + 1) R hR z -
          vladimirov_psi_schwartz (n + 1) R hR z -
          vladimirov_deriv_psi_schwartz (n + 1) R hR z (z - z))) p‖ ≤
      M * ‖z - z‖ ^ 2 := by
  have h1 : z - z = 0 := sub_self z
  rw [h1, vladimirov_deriv_psi_zero]
  have h2 : (vladimirov_psi_schwartz (n + 1) R hR z -
      vladimirov_psi_schwartz (n + 1) R hR z - 0) = 0 := by simp
  rw [h2]
  simp only [FunLike.coe_zero, Pi.zero_apply, iteratedFDeriv_zero, norm_zero]
  simp

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_phase_bound_sq (n : ℕ) (h : Fin (n + 1) → Fin 4 → ℂ)
    (p : Fin (n + 1) → Fin 4 → ℝ) :
    ‖vladimirov_phase_CLM (n + 1) h p‖ ^ 2 ≤ ‖vladimirov_phase_z_CLM (n + 1) p‖ ^ 2 * ‖h‖ ^ 2 := by
  have h_bound := vladimirov_phase_bound (n + 1) h p
  have h_sq : ‖vladimirov_phase_CLM (n + 1) h p‖ ^ 2 ≤
      (‖vladimirov_phase_z_CLM (n + 1) p‖ * ‖h‖) ^ 2 := by
    nlinarith [norm_nonneg (vladimirov_phase_CLM (n + 1) h p),
               norm_nonneg (vladimirov_phase_z_CLM (n + 1) p),
               norm_nonneg h]
  rwa [mul_pow] at h_sq

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_psi_taylor_succ_norm_le_ratio (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z x' : Fin (n + 1) → Fin 4 → ℂ) (p : Fin (n + 1) → Fin 4 → ℝ) (m : ℕ) :
    ‖iteratedFDeriv ℝ (m + 1)
       (⇑(vladimirov_psi_schwartz (n + 1) R hR x' -
          vladimirov_psi_schwartz (n + 1) R hR z -
          vladimirov_deriv_psi_schwartz (n + 1) R hR z (x' - z))) p‖ ≤
      (schwartz_single_seminorm_ratio (n + 1) R hR z (0, m + 1) x') * ‖x' - z‖ ^ 2 := by
  have h_norm := norm_iteratedFDeriv_le_seminorm n R hR z x' p m
  have h_ratio := seminorm_le_single_ratio_mul_sq (n + 1) R hR z (0, m + 1) x'
  exact h_norm.trans h_ratio

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_psi_taylor_succ_compact_pointwise_bound_of_eq (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z x' : Fin (n + 1) → Fin 4 → ℂ) (p : Fin (n + 1) → Fin 4 → ℝ) (m : ℕ)
    (h_eq : x' = z) (M : ℝ)
    (hM : Real.exp (‖vladimirov_phase_CLM (n + 1) z‖ * (2 * R)) *
      (‖vladimirov_phase_z_CLM (n + 1) p‖ + 1) ^ 2 ≤ M) :
    ‖iteratedFDeriv ℝ (m + 1)
       (⇑(vladimirov_psi_schwartz (n + 1) R hR x' -
          vladimirov_psi_schwartz (n + 1) R hR z -
          vladimirov_deriv_psi_schwartz (n + 1) R hR z (x' - z))) p‖ ≤
      M * ‖x' - z‖ ^ 2 := by
  have hM_nonneg : 0 ≤ M := by
    have h1 : 0 ≤ Real.exp (‖vladimirov_phase_CLM (n + 1) z‖ * (2 * R)) *
      (‖vladimirov_phase_z_CLM (n + 1) p‖ + 1) ^ 2 := by positivity
    exact h1.trans hM
  rw [h_eq]
  exact vladimirov_psi_taylor_succ_compact_pointwise_bound_eq n R hR z p m M hM_nonneg

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_psi_taylor_succ_compact_pointwise_bound_of_ne (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z x' : Fin (n + 1) → Fin 4 → ℂ) (p : Fin (n + 1) → Fin 4 → ℝ) (m : ℕ)
    (_h_ne : x' ≠ z) (_hp : ‖p‖ ≤ 2 * R) (_hx' : x' ∈ Metric.closedBall z 1) (M : ℝ)
    (h_ratio_le : schwartz_single_seminorm_ratio (n + 1) R hR z (0, m + 1) x' ≤ M) :
    ‖iteratedFDeriv ℝ (m + 1)
       (⇑(vladimirov_psi_schwartz (n + 1) R hR x' -
          vladimirov_psi_schwartz (n + 1) R hR z -
          vladimirov_deriv_psi_schwartz (n + 1) R hR z (x' - z))) p‖ ≤
      M * ‖x' - z‖ ^ 2 := by
  have h_bound := vladimirov_psi_taylor_succ_norm_le_ratio n R hR z x' p m
  have h_mul : (schwartz_single_seminorm_ratio (n + 1) R hR z (0, m + 1) x' * ‖x' - z‖ ^ 2) ≤
      M * ‖x' - z‖ ^ 2 := by gcongr
  exact h_bound.trans h_mul

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_psi_taylor_succ_deriv_eq (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z x' : Fin (n + 1) → Fin 4 → ℂ) (p : Fin (n + 1) → Fin 4 → ℝ) (m : ℕ) :
    iteratedFDeriv ℝ (m + 1)
       (⇑(vladimirov_psi_schwartz (n + 1) R hR x' -
          vladimirov_psi_schwartz (n + 1) R hR z -
          vladimirov_deriv_psi_schwartz (n + 1) R hR z (x' - z))) p =
    iteratedFDeriv ℝ (m + 1)
       (fun q => vladimirov_psi (n + 1) R hR z q *
         (Complex.exp (vladimirov_phase_CLM (n + 1) (x' - z) q) - 1 -
          vladimirov_phase_CLM (n + 1) (x' - z) q)) p := by
  have h_ext := vladimirov_psi_taylor_funext n R hR z x'
  rw [h_ext]

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_psi_taylor_succ_compact_pointwise_bound_of_ratio_le (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z x' : Fin (n + 1) → Fin 4 → ℂ) (p : Fin (n + 1) → Fin 4 → ℝ) (m : ℕ)
    (hp : ‖p‖ ≤ 2 * R) (hx' : x' ∈ Metric.closedBall z 1) (M : ℝ)
    (hM : Real.exp (‖vladimirov_phase_CLM (n + 1) z‖ * (2 * R)) *
      (‖vladimirov_phase_z_CLM (n + 1) p‖ + 1) ^ 2 ≤ M)
    (h_ratio_le : schwartz_single_seminorm_ratio (n + 1) R hR z (0, m + 1) x' ≤ M) :
    ‖iteratedFDeriv ℝ (m + 1)
       (⇑(vladimirov_psi_schwartz (n + 1) R hR x' -
          vladimirov_psi_schwartz (n + 1) R hR z -
          vladimirov_deriv_psi_schwartz (n + 1) R hR z (x' - z))) p‖ ≤
      M * ‖x' - z‖ ^ 2 := by
  by_cases h_eq : x' = z
  · exact vladimirov_psi_taylor_succ_compact_pointwise_bound_of_eq n R hR z x' p m h_eq M hM
  · exact vladimirov_psi_taylor_succ_compact_pointwise_bound_of_ne n R hR z x' p m
      h_eq hp hx' M h_ratio_le

omit [Fintype ι] [DecidableEq ι] in
lemma sq_norm_sub_pos_of_ne {E : Type*} [NormedAddCommGroup E] {x' z : E} (h : x' ≠ z) :
    0 < ‖x' - z‖ ^ 2 :=
  sq_pos_of_ne_zero (norm_ne_zero_iff.mpr (sub_ne_zero.mpr h))

omit [Fintype ι] [DecidableEq ι] in
lemma norm_le_mul_sq_iff_div_le {E : Type*} [NormedAddCommGroup E] {x' z : E} (h : x' ≠ z)
    (a M : ℝ) :
    a ≤ M * ‖x' - z‖ ^ 2 ↔ a / ‖x' - z‖ ^ 2 ≤ M := by
  have h_pos := sq_norm_sub_pos_of_ne h
  rw [div_le_iff₀ h_pos]

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_psi_taylor_succ_pointwise_ratio_le_seminorm_ratio (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z x' : Fin (n + 1) → Fin 4 → ℂ) (p : Fin (n + 1) → Fin 4 → ℝ) (m : ℕ)
    (h_ne : x' ≠ z) :
    ‖iteratedFDeriv ℝ (m + 1)
       (⇑(vladimirov_psi_schwartz (n + 1) R hR x' -
          vladimirov_psi_schwartz (n + 1) R hR z -
          vladimirov_deriv_psi_schwartz (n + 1) R hR z (x' - z))) p‖ / ‖x' - z‖ ^ 2 ≤
      schwartz_single_seminorm_ratio (n + 1) R hR z (0, m + 1) x' := by
  have h_pos := sq_norm_sub_pos_of_ne h_ne
  rw [div_le_iff₀ h_pos]
  exact vladimirov_psi_taylor_succ_norm_le_ratio n R hR z x' p m

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_psi_taylor_succ_deriv_norm_le_of_ratio (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z x' : Fin (n + 1) → Fin 4 → ℂ) (p : Fin (n + 1) → Fin 4 → ℝ) (m : ℕ)
    (h_ne : x' ≠ z) (M : ℝ)
    (h_ratio : schwartz_single_seminorm_ratio (n + 1) R hR z (0, m + 1) x' ≤ M) :
    ‖iteratedFDeriv ℝ (m + 1)
       (⇑(vladimirov_psi_schwartz (n + 1) R hR x' -
          vladimirov_psi_schwartz (n + 1) R hR z -
          vladimirov_deriv_psi_schwartz (n + 1) R hR z (x' - z))) p‖ ≤
      M * ‖x' - z‖ ^ 2 := by
  have h_norm := norm_le_mul_sq_iff_div_le h_ne
    ‖iteratedFDeriv ℝ (m + 1)
       (⇑(vladimirov_psi_schwartz (n + 1) R hR x' -
          vladimirov_psi_schwartz (n + 1) R hR z -
          vladimirov_deriv_psi_schwartz (n + 1) R hR z (x' - z))) p‖ M
  rw [h_norm]
  have h_le := vladimirov_psi_taylor_succ_pointwise_ratio_le_seminorm_ratio n R hR z x' p m h_ne
  exact h_le.trans h_ratio

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_psi_taylor_succ_compact_pointwise_bound_closed (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z x' : Fin (n + 1) → Fin 4 → ℂ) (p : Fin (n + 1) → Fin 4 → ℝ) (m : ℕ)
    (_hp : ‖p‖ ≤ 2 * R) (_hx' : x' ∈ Metric.closedBall z 1) (M : ℝ)
    (hM : Real.exp (‖vladimirov_phase_CLM (n + 1) z‖ * (2 * R)) *
      (‖vladimirov_phase_z_CLM (n + 1) p‖ + 1) ^ 2 ≤ M)
    (h_ratio : schwartz_single_seminorm_ratio (n + 1) R hR z (0, m + 1) x' ≤ M) :
    ‖iteratedFDeriv ℝ (m + 1)
       (⇑(vladimirov_psi_schwartz (n + 1) R hR x' -
          vladimirov_psi_schwartz (n + 1) R hR z -
          vladimirov_deriv_psi_schwartz (n + 1) R hR z (x' - z))) p‖ ≤
      M * ‖x' - z‖ ^ 2 := by
  by_cases h_eq : x' = z
  · exact vladimirov_psi_taylor_succ_compact_pointwise_bound_of_eq n R hR z x' p m h_eq M hM
  · exact vladimirov_psi_taylor_succ_deriv_norm_le_of_ratio n R hR z x' p m h_eq M h_ratio

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_phase_sq_factor (n : ℕ) (z x' : Fin (n + 1) → Fin 4 → ℂ)
    (p : Fin (n + 1) → Fin 4 → ℝ) :
    ‖vladimirov_phase_CLM (n + 1) (x' - z) p‖ ^ 2 ≤
      ‖vladimirov_phase_z_CLM (n + 1) p‖ ^ 2 * ‖x' - z‖ ^ 2 :=
  vladimirov_phase_bound_sq n (x' - z) p

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_taylor_kernel_norm_le (n : ℕ) (z x' : Fin (n + 1) → Fin 4 → ℂ)
    (p : Fin (n + 1) → Fin 4 → ℝ)
    (hu : ‖vladimirov_phase_CLM (n + 1) (x' - z) p‖ ≤ 1) :
    ‖Complex.exp (vladimirov_phase_CLM (n + 1) (x' - z) p) - 1 -
      vladimirov_phase_CLM (n + 1) (x' - z) p‖ ≤
      ‖vladimirov_phase_z_CLM (n + 1) p‖ ^ 2 * ‖x' - z‖ ^ 2 := by
  have h_exp := exp_sub_one_sub_id_bound (vladimirov_phase_CLM (n + 1) (x' - z) p) hu
  have h_sq := vladimirov_phase_sq_factor n z x' p
  exact h_exp.trans h_sq

lemma norm_iteratedFDeriv_comp_clm_le {E G F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : G →L[ℝ] E) (f : E → F) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (x : G) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (f ∘ L) x‖ ≤ ‖iteratedFDeriv ℝ j f (L x)‖ * ‖L‖ ^ j := by
  rw [ContinuousLinearMap.iteratedFDeriv_comp_right L hf x (WithTop.coe_le_coe.mpr le_top)]
  have h_le := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv ℝ j f (L x)) (fun _ : Fin j => L)
  have h_prod : ∏ _i : Fin j, ‖L‖ = ‖L‖ ^ j := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rwa [h_prod] at h_le

noncomputable def taylor_kernel_1d (w : ℂ) : ℂ := Complex.exp w - 1 - w

lemma taylor_kernel_1d_contDiff : ContDiff ℝ (⊤ : ℕ∞) taylor_kernel_1d := by
  have h_exp : ContDiff ℝ (⊤ : ℕ∞) Complex.exp := Complex.contDiff_exp
  have h_id : ContDiff ℝ (⊤ : ℕ∞) (id : ℂ → ℂ) := contDiff_id
  exact (h_exp.sub contDiff_const).sub h_id

omit [Fintype ι] [DecidableEq ι] in
lemma taylor_kernel_eq_comp (n : ℕ) (h : Fin (n + 1) → Fin 4 → ℂ) :
    (fun q : Fin (n + 1) → Fin 4 → ℝ =>
      Complex.exp ((vladimirov_phase_CLM (n + 1) h) q) - 1 - (vladimirov_phase_CLM (n + 1) h) q) =
    taylor_kernel_1d ∘ (vladimirov_phase_CLM (n + 1) h) := rfl

omit [Fintype ι] [DecidableEq ι] in
lemma taylor_kernel_contDiff (n : ℕ) (h : Fin (n + 1) → Fin 4 → ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun q : Fin (n + 1) → Fin 4 → ℝ =>
      Complex.exp ((vladimirov_phase_CLM (n + 1) h) q) - 1 -
        (vladimirov_phase_CLM (n + 1) h) q) := by
  rw [taylor_kernel_eq_comp]
  exact taylor_kernel_1d_contDiff.comp (vladimirov_phase_CLM (n + 1) h).contDiff

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_phase_clm_norm_le (n : ℕ) :
    ∃ C_L : ℝ, 0 ≤ C_L ∧ ∀ h, ‖vladimirov_phase_CLM (n + 1) h‖ ≤ C_L * ‖h‖ := by
  obtain ⟨C_L, hC_L_nonneg, hC_L⟩ := vladimirov_phase_z_clm_ball_bound n 1 zero_lt_one
  use C_L
  refine ⟨hC_L_nonneg, ?_⟩
  intro h
  have h_bound_nonneg : 0 ≤ C_L * ‖h‖ := mul_nonneg hC_L_nonneg (norm_nonneg h)
  refine ContinuousLinearMap.opNorm_le_bound _ h_bound_nonneg fun p => ?_
  by_cases hp : p = 0
  · subst hp
    simp only [map_zero, norm_zero, mul_zero]
    exact le_rfl
  · have hp_norm_pos : 0 < ‖p‖ := norm_pos_iff.mpr hp
    let p_unit := ‖p‖⁻¹ • p
    have hp_unit_norm : ‖p_unit‖ = 1 := by
      dsimp [p_unit]
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (ne_of_gt hp_norm_pos)]
    have hp_unit_le : ‖p_unit‖ ≤ 2 * 1 := by
      rw [hp_unit_norm]
      linarith
    have h_unit_bound := hC_L p_unit hp_unit_le
    have h_phase := vladimirov_phase_bound (n + 1) h p_unit
    have h_p_eq : p = ‖p‖ • p_unit := by
      dsimp [p_unit]
      rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hp_norm_pos), one_smul]
    conv_lhs => rw [h_p_eq]
    rw [ContinuousLinearMap.map_smul_of_tower, norm_smul, norm_norm]
    calc ‖p‖ * ‖vladimirov_phase_CLM (n + 1) h p_unit‖
        ≤ ‖p‖ * (‖vladimirov_phase_z_CLM (n + 1) p_unit‖ * ‖h‖) := by gcongr
      _ ≤ ‖p‖ * (C_L * ‖h‖) := by gcongr
      _ = (C_L * ‖h‖) * ‖p‖ := by ring

lemma taylor_kernel_1d_fderiv_norm_le {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ‖fderiv ℝ taylor_kernel_1d w‖ ≤ 2 * ‖w‖ := by
  have h_diff : DifferentiableAt ℂ taylor_kernel_1d w := by
    have h1 : DifferentiableAt ℂ Complex.exp w := Complex.differentiable_exp.differentiableAt
    have h2 : DifferentiableAt ℂ (fun _ => (1 : ℂ)) w := differentiableAt_const _
    have h3 : DifferentiableAt ℂ id w := differentiableAt_id
    exact (h1.sub h2).sub h3
  rw [h_diff.fderiv_restrictScalars (𝕜 := ℝ)]
  rw [ContinuousLinearMap.norm_restrictScalars]
  rw [← norm_deriv_eq_norm_fderiv]
  have h_deriv : deriv taylor_kernel_1d w = Complex.exp w - 1 := by
    have h1 : HasDerivAt Complex.exp (Complex.exp w) w := Complex.hasDerivAt_exp w
    have h2 : HasDerivAt (fun _ => (1 : ℂ)) 0 w := hasDerivAt_const w 1
    have h3 : HasDerivAt id 1 w := hasDerivAt_id w
    have h_total := (h1.sub h2).sub h3
    simp only [sub_zero] at h_total
    exact h_total.deriv
  rw [h_deriv]
  exact Complex.norm_exp_sub_one_le hw

lemma taylor_kernel_1d_deriv_locally_bounded (j : ℕ) :
    ∃ K > 0, ∀ᶠ w in 𝓝 0, ‖iteratedFDeriv ℝ j taylor_kernel_1d w‖ ≤ K := by
  have h_cont : Continuous (iteratedFDeriv ℝ j taylor_kernel_1d) :=
    taylor_kernel_1d_contDiff.continuous_iteratedFDeriv (mod_cast le_top)
  have h_norm_cont : ContinuousAt (fun w ↦ ‖iteratedFDeriv ℝ j taylor_kernel_1d w‖) 0 :=
    h_cont.norm.continuousAt
  let K := ‖iteratedFDeriv ℝ j taylor_kernel_1d 0‖ + 1
  have hK_pos : 0 < K := by positivity
  refine ⟨K, hK_pos, ?_⟩
  have h_lt : ‖iteratedFDeriv ℝ j taylor_kernel_1d 0‖ < K := lt_add_one _
  exact (h_norm_cont.eventually (gt_mem_nhds h_lt)).mono fun w hw ↦ le_of_lt hw

omit [Fintype ι] [DecidableEq ι] in
lemma schwartz_single_seminorm_ratio_bounded_of_pointwise_bound
    (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z : Fin (n + 1) → Fin 4 → ℂ) (m : ℕ)
    (M : ℝ) (hM_nonneg : 0 ≤ M)
    (h_pointwise : ∀ᶠ x' in 𝓝 z, ∀ p, ‖p‖ ≤ 2 * R →
      ‖iteratedFDeriv ℝ (m + 1)
         (⇑(vladimirov_psi_schwartz (n + 1) R hR x' -
            vladimirov_psi_schwartz (n + 1) R hR z -
            vladimirov_deriv_psi_schwartz (n + 1) R hR z (x' - z))) p‖ ≤
        M * ‖x' - z‖ ^ 2) :
    ∀ᶠ x' in 𝓝 z,
      schwartz_single_seminorm_ratio (n + 1) R hR z (0, m + 1) x' ≤ M := by
  filter_upwards [h_pointwise] with x' hx'
  by_cases h_eq : x' = z
  · subst h_eq
    rw [schwartz_single_seminorm_ratio, if_pos rfl]
    exact hM_nonneg
  · rw [schwartz_single_seminorm_ratio_le_iff _ _ _ _ _ _ _ hM_nonneg]
    change (SchwartzMap.seminorm ℝ 0 (m + 1))
        (vladimirov_psi_schwartz (n + 1) R hR x' -
         vladimirov_psi_schwartz (n + 1) R hR z -
         vladimirov_deriv_psi_schwartz (n + 1) R hR z (x' - z)) ≤ M * ‖x' - z‖ ^ 2
    have h_bound_nonneg : 0 ≤ M * ‖x' - z‖ ^ 2 := mul_nonneg hM_nonneg (sq_nonneg _)
    refine seminorm_succ_le_of_pointwise_bound (n + 1) R hR z x' 0 m
      (M * ‖x' - z‖ ^ 2) h_bound_nonneg ?_
    intro p
    simp only [pow_zero, one_mul]
    by_cases hp : ‖p‖ ≤ 2 * R
    · exact hx' p hp
    · have hp_lt : 2 * R < ‖p‖ := not_le.mp hp
      have hz := vladimirov_psi_taylor_succ_zero_of_lt n R hR z x' p m hp_lt
      rw [hz, norm_zero]
      exact h_bound_nonneg

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_psi_deriv_norm_le_seminorm (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z : Fin (n + 1) → Fin 4 → ℂ) (i : ℕ) (p : Fin (n + 1) → Fin 4 → ℝ) :
    ‖iteratedFDeriv ℝ i (vladimirov_psi (n + 1) R hR z) p‖ ≤
      SchwartzMap.seminorm ℝ 0 i (vladimirov_psi_schwartz (n + 1) R hR z) := by
  have h := SchwartzMap.le_seminorm (𝕜 := ℝ) 0 i (vladimirov_psi_schwartz (n + 1) R hR z) p
  simp only [pow_zero, one_mul] at h
  exact h

omit [Fintype ι] [DecidableEq ι] in
lemma taylor_kernel_deriv_zero_bound (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z : Fin (n + 1) → Fin 4 → ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x' in 𝓝 z, ∀ p, ‖p‖ ≤ 2 * R →
      ‖iteratedFDeriv ℝ 0
          (fun q ↦ Complex.exp ((vladimirov_phase_CLM (n + 1) (x' - z)) q) - 1 -
            (vladimirov_phase_CLM (n + 1) (x' - z)) q) p‖ ≤
        C * ‖x' - z‖ ^ 2 := by
  obtain ⟨B, hB_nonneg, hB⟩ := vladimirov_phase_z_clm_ball_bound n R hR
  have hB_pos : 0 < B + 1 := by linarith
  have hδ_pos : 0 < (B + 1)⁻¹ := inv_pos.mpr hB_pos
  use B ^ 2
  refine ⟨sq_nonneg B, ?_⟩
  have h_nhds : Metric.closedBall z (B + 1)⁻¹ ∈ 𝓝 z := Metric.closedBall_mem_nhds z hδ_pos
  filter_upwards [h_nhds] with x' hx' p hp
  rw [norm_iteratedFDeriv_zero]
  have h_dist : ‖x' - z‖ ≤ (B + 1)⁻¹ := by
    rw [Metric.mem_closedBall, dist_eq_norm] at hx'
    exact hx'
  have h_phase := vladimirov_phase_bound (n + 1) (x' - z) p
  have h_Bp := hB p hp
  have h_u : ‖vladimirov_phase_CLM (n + 1) (x' - z) p‖ ≤ 1 := by
    calc ‖vladimirov_phase_CLM (n + 1) (x' - z) p‖
        ≤ ‖vladimirov_phase_z_CLM (n + 1) p‖ * ‖x' - z‖ := h_phase
      _ ≤ B * (B + 1)⁻¹ := by gcongr
      _ ≤ (B + 1) * (B + 1)⁻¹ := by gcongr; linarith
      _ = 1 := mul_inv_cancel₀ (ne_of_gt hB_pos)
  have h_taylor := vladimirov_taylor_kernel_norm_le n z x' p h_u
  calc ‖Complex.exp ((vladimirov_phase_CLM (n + 1) (x' - z)) p) - 1 -
        (vladimirov_phase_CLM (n + 1) (x' - z)) p‖
      ≤ ‖vladimirov_phase_z_CLM (n + 1) p‖ ^ 2 * ‖x' - z‖ ^ 2 := h_taylor
    _ ≤ B ^ 2 * ‖x' - z‖ ^ 2 := by gcongr

omit [Fintype ι] [DecidableEq ι] in
lemma taylor_kernel_deriv_ge_two_bound (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z : Fin (n + 1) → Fin 4 → ℂ) (j : ℕ) (hj : 2 ≤ j) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x' in 𝓝 z, ∀ p, ‖p‖ ≤ 2 * R →
      ‖iteratedFDeriv ℝ j
          (fun q ↦ Complex.exp ((vladimirov_phase_CLM (n + 1) (x' - z)) q) - 1 -
            (vladimirov_phase_CLM (n + 1) (x' - z)) q) p‖ ≤
        C * ‖x' - z‖ ^ 2 := by
  obtain ⟨K, hK_pos, hK⟩ := taylor_kernel_1d_deriv_locally_bounded j
  obtain ⟨ε, hε_pos, hε⟩ := Metric.eventually_nhds_iff.mp hK
  obtain ⟨B, hB_nonneg, hB⟩ := vladimirov_phase_z_clm_ball_bound n R hR
  obtain ⟨C_L, hC_L_nonneg, hC_L⟩ := vladimirov_phase_clm_norm_le n
  have hB_pos : 0 < B + 1 := by linarith
  have h_ratio_pos : 0 < ε / (B + 1) := div_pos hε_pos hB_pos
  let δ := min (1 : ℝ) (ε / (B + 1))
  have hδ_pos : 0 < δ := lt_min zero_lt_one h_ratio_pos
  use K * C_L ^ j
  refine ⟨mul_nonneg (le_of_lt hK_pos) (pow_nonneg hC_L_nonneg j), ?_⟩
  have h_nhds : Metric.ball z δ ∈ 𝓝 z := Metric.ball_mem_nhds z hδ_pos
  filter_upwards [h_nhds] with x' hx' p hp
  have h_dist : ‖x' - z‖ < δ := by
    rw [Metric.mem_ball, dist_eq_norm] at hx'
    exact hx'
  have h_dist_one : ‖x' - z‖ ≤ 1 := (le_of_lt h_dist).trans (min_le_left 1 _)
  have h_dist_ε : ‖x' - z‖ < ε / (B + 1) := h_dist.trans_le (min_le_right 1 _)
  let L := vladimirov_phase_CLM (n + 1) (x' - z)
  have h_comp : (fun q ↦ Complex.exp (L q) - 1 - L q) = taylor_kernel_1d ∘ L := rfl
  rw [h_comp]
  have h_le := norm_iteratedFDeriv_comp_clm_le L taylor_kernel_1d taylor_kernel_1d_contDiff p j
  have h_Bp := hB p hp
  have h_phase := vladimirov_phase_bound (n + 1) (x' - z) p
  have h_Lp_lt : ‖L p‖ < ε := by
    have h1 : ‖L p‖ ≤ B * ‖x' - z‖ := by
      calc ‖L p‖ ≤ ‖vladimirov_phase_z_CLM (n + 1) p‖ * ‖x' - z‖ := h_phase
        _ ≤ B * ‖x' - z‖ := by gcongr
    have h2 : B * ‖x' - z‖ < ε := by
      calc B * ‖x' - z‖
          ≤ (B + 1) * ‖x' - z‖ := by nlinarith [norm_nonneg (x' - z)]
        _ < (B + 1) * (ε / (B + 1)) := by nlinarith [hB_pos, h_dist_ε]
        _ = ε := mul_div_cancel₀ ε (ne_of_gt hB_pos)
    exact h1.trans_lt h2
  have h_ball_ε : L p ∈ Metric.ball (0 : ℂ) ε := by
    rw [Metric.mem_ball, dist_zero_right]
    exact h_Lp_lt
  have h_K_bound : ‖iteratedFDeriv ℝ j taylor_kernel_1d (L p)‖ ≤ K := hε h_ball_ε
  have hL_le : ‖L‖ ≤ C_L * ‖x' - z‖ := hC_L (x' - z)
  have hL_le_C : ‖L‖ ≤ C_L := by
    calc ‖L‖ ≤ C_L * ‖x' - z‖ := hL_le
      _ ≤ C_L * 1 := by gcongr
      _ = C_L := mul_one _
  rcases Nat.le.dest hj with ⟨k, rfl⟩
  rw [Nat.add_comm 2 k]
  rw [Nat.add_comm 2 k] at h_le h_K_bound
  have h_pow : ‖L‖ ^ k * ‖L‖ ^ 2 ≤ C_L ^ k * C_L ^ 2 * ‖x' - z‖ ^ 2 := by
    calc ‖L‖ ^ k * ‖L‖ ^ 2
        ≤ C_L ^ k * (C_L * ‖x' - z‖) ^ 2 := by gcongr
      _ = C_L ^ k * (C_L ^ 2 * ‖x' - z‖ ^ 2) := by ring
      _ = C_L ^ k * C_L ^ 2 * ‖x' - z‖ ^ 2 := by ring
  calc ‖iteratedFDeriv ℝ (k + 2) (taylor_kernel_1d ∘ L) p‖
      ≤ ‖iteratedFDeriv ℝ (k + 2) taylor_kernel_1d (L p)‖ * ‖L‖ ^ (k + 2) := h_le
    _ ≤ K * ‖L‖ ^ (k + 2) := by gcongr
    _ = K * (‖L‖ ^ k * ‖L‖ ^ 2) := by rw [pow_add]
    _ ≤ K * (C_L ^ k * C_L ^ 2 * ‖x' - z‖ ^ 2) := by gcongr
    _ = (K * (C_L ^ k * C_L ^ 2)) * ‖x' - z‖ ^ 2 := by ring
    _ = (K * C_L ^ (k + 2)) * ‖x' - z‖ ^ 2 := by rw [← pow_add]

omit [Fintype ι] [DecidableEq ι] in
lemma taylor_kernel_deriv_one_bound (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z : Fin (n + 1) → Fin 4 → ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x' in 𝓝 z, ∀ p, ‖p‖ ≤ 2 * R →
      ‖iteratedFDeriv ℝ 1
          (fun q ↦ Complex.exp ((vladimirov_phase_CLM (n + 1) (x' - z)) q) - 1 -
            (vladimirov_phase_CLM (n + 1) (x' - z)) q) p‖ ≤
        C * ‖x' - z‖ ^ 2 := by
  obtain ⟨B, hB_nonneg, hB⟩ := vladimirov_phase_z_clm_ball_bound n R hR
  obtain ⟨C_L, hC_L_nonneg, hC_L⟩ := vladimirov_phase_clm_norm_le n
  have hB_pos : 0 < B + 1 := by linarith
  have hδ_pos : 0 < (B + 1)⁻¹ := inv_pos.mpr hB_pos
  use 2 * B * C_L
  refine ⟨by positivity, ?_⟩
  have h_nhds : Metric.closedBall z (B + 1)⁻¹ ∈ 𝓝 z := Metric.closedBall_mem_nhds z hδ_pos
  filter_upwards [h_nhds] with x' hx' p hp
  have h_dist : ‖x' - z‖ ≤ (B + 1)⁻¹ := by
    rw [Metric.mem_closedBall, dist_eq_norm] at hx'
    exact hx'
  let L := vladimirov_phase_CLM (n + 1) (x' - z)
  have h_comp : (fun q ↦ Complex.exp (L q) - 1 - L q) = taylor_kernel_1d ∘ L := rfl
  rw [h_comp]
  have h_le := norm_iteratedFDeriv_comp_clm_le L taylor_kernel_1d taylor_kernel_1d_contDiff p 1
  have h_Bp := hB p hp
  have h_phase := vladimirov_phase_bound (n + 1) (x' - z) p
  have h_u : ‖L p‖ ≤ 1 := by
    calc ‖L p‖
        ≤ ‖vladimirov_phase_z_CLM (n + 1) p‖ * ‖x' - z‖ := h_phase
      _ ≤ B * (B + 1)⁻¹ := by gcongr
      _ ≤ (B + 1) * (B + 1)⁻¹ := by gcongr; linarith
      _ = 1 := mul_inv_cancel₀ (ne_of_gt hB_pos)
  have h_Lp_le : ‖L p‖ ≤ B * ‖x' - z‖ := by
    calc ‖L p‖ ≤ ‖vladimirov_phase_z_CLM (n + 1) p‖ * ‖x' - z‖ := h_phase
      _ ≤ B * ‖x' - z‖ := by gcongr
  have h_fderiv := taylor_kernel_1d_fderiv_norm_le h_u
  have hL_le : ‖L‖ ≤ C_L * ‖x' - z‖ := hC_L (x' - z)
  calc ‖iteratedFDeriv ℝ 1 (taylor_kernel_1d ∘ L) p‖
      ≤ ‖iteratedFDeriv ℝ 1 taylor_kernel_1d (L p)‖ * ‖L‖ ^ 1 := h_le
    _ = ‖fderiv ℝ taylor_kernel_1d (L p)‖ * ‖L‖ := by rw [norm_iteratedFDeriv_one, pow_one]
    _ ≤ (2 * ‖L p‖) * (C_L * ‖x' - z‖) := by gcongr
    _ ≤ (2 * (B * ‖x' - z‖)) * (C_L * ‖x' - z‖) := by gcongr
    _ = (2 * B * C_L) * ‖x' - z‖ ^ 2 := by ring

omit [Fintype ι] [DecidableEq ι] in
lemma taylor_kernel_deriv_bound (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z : Fin (n + 1) → Fin 4 → ℂ) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x' in 𝓝 z, ∀ p, ‖p‖ ≤ 2 * R →
      ‖iteratedFDeriv ℝ j
          (fun q ↦ Complex.exp ((vladimirov_phase_CLM (n + 1) (x' - z)) q) - 1 -
            (vladimirov_phase_CLM (n + 1) (x' - z)) q) p‖ ≤
        C * ‖x' - z‖ ^ 2 := by
  rcases j with _|j
  · exact taylor_kernel_deriv_zero_bound n R hR z
  · rcases j with _|j
    · exact taylor_kernel_deriv_one_bound n R hR z
    · exact taylor_kernel_deriv_ge_two_bound n R hR z (j + 2) (by omega)

omit [Fintype ι] [DecidableEq ι] in
lemma schwartz_single_seminorm_ratio_bounded_zero_succ (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z : Fin (n + 1) → Fin 4 → ℂ) (m : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ x' in 𝓝 z,
      schwartz_single_seminorm_ratio (n + 1) R hR z (0, m + 1) x' ≤ M := by
  choose C hC using fun j => taylor_kernel_deriv_bound n R hR z j
  let M := ∑ i ∈ Finset.range (m + 2),
    ((m + 1).choose i : ℝ) *
      SchwartzMap.seminorm ℝ 0 i (vladimirov_psi_schwartz (n + 1) R hR z) *
      C (m + 1 - i)
  have hM_nonneg : 0 ≤ M := by
    refine Finset.sum_nonneg fun i _ => ?_
    refine mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (apply_nonneg _ _)) (hC (m + 1 - i)).1
  use M
  refine ⟨hM_nonneg, ?_⟩
  apply schwartz_single_seminorm_ratio_bounded_of_pointwise_bound n R hR z m M hM_nonneg
  have h_all : ∀ᶠ x' in 𝓝 z, ∀ i ∈ Finset.range (m + 2), ∀ p, ‖p‖ ≤ 2 * R →
      ‖iteratedFDeriv ℝ (m + 1 - i)
          (fun q ↦ Complex.exp ((vladimirov_phase_CLM (n + 1) (x' - z)) q) - 1 -
            (vladimirov_phase_CLM (n + 1) (x' - z)) q) p‖ ≤
        C (m + 1 - i) * ‖x' - z‖ ^ 2 := by
    rw [eventually_all_finset]
    intro i _
    exact (hC (m + 1 - i)).2
  filter_upwards [h_all] with x' hx' p hp
  have h_mul_le := norm_iteratedFDeriv_mul_le (n := m + 1)
    (vladimirov_psi_contDiff (n + 1) R hR z)
    (taylor_kernel_contDiff n (x' - z)) p (WithTop.coe_le_coe.mpr le_top)
  rw [vladimirov_psi_taylor_succ_deriv_eq]
  refine h_mul_le.trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi => ?_
  have h_psi := vladimirov_psi_deriv_norm_le_seminorm n R hR z i p
  have h_kernel := hx' i hi p hp
  calc ((m + 1).choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (vladimirov_psi (n + 1) R hR z) p‖ *
        ‖iteratedFDeriv ℝ (m + 1 - i)
            (fun q ↦
              Complex.exp ((vladimirov_phase_CLM (n + 1) (x' - z)) q) - 1 -
                (vladimirov_phase_CLM (n + 1) (x' - z)) q) p‖
      ≤ ((m + 1).choose i : ℝ) *
          SchwartzMap.seminorm ℝ 0 i (vladimirov_psi_schwartz (n + 1) R hR z) *
          (C (m + 1 - i) * ‖x' - z‖ ^ 2) := by gcongr
    _ = (((m + 1).choose i : ℝ) *
          SchwartzMap.seminorm ℝ 0 i (vladimirov_psi_schwartz (n + 1) R hR z) *
          C (m + 1 - i)) * ‖x' - z‖ ^ 2 := by ring

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_psi_taylor_succ_unif_bound_exists (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z : Fin (n + 1) → Fin 4 → ℂ) (m : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ x' in 𝓝 z,
      ∀ p, ‖p‖ ≤ 2 * R →
        ‖iteratedFDeriv ℝ (m + 1)
           (⇑(vladimirov_psi_schwartz (n + 1) R hR x' -
              vladimirov_psi_schwartz (n + 1) R hR z -
              vladimirov_deriv_psi_schwartz (n + 1) R hR z (x' - z))) p‖ ≤
          M * ‖x' - z‖ ^ 2 := by
  obtain ⟨M, hM_nonneg, hM⟩ := schwartz_single_seminorm_ratio_bounded_zero_succ n R hR z m
  use M
  refine ⟨hM_nonneg, ?_⟩
  filter_upwards [hM] with x' hx' p _hp
  have h_norm := norm_iteratedFDeriv_le_seminorm n R hR z x' p m
  have h_ratio := seminorm_le_single_ratio_mul_sq (n + 1) R hR z (0, m + 1) x'
  calc ‖iteratedFDeriv ℝ (m + 1)
         (⇑(vladimirov_psi_schwartz (n + 1) R hR x' -
            vladimirov_psi_schwartz (n + 1) R hR z -
            vladimirov_deriv_psi_schwartz (n + 1) R hR z (x' - z))) p‖
      ≤ (SchwartzMap.seminorm ℝ 0 (m + 1))
          (vladimirov_psi_schwartz (n + 1) R hR x' -
           vladimirov_psi_schwartz (n + 1) R hR z -
           vladimirov_deriv_psi_schwartz (n + 1) R hR z (x' - z)) := h_norm
    _ ≤ (schwartz_single_seminorm_ratio (n + 1) R hR z (0, m + 1) x') * ‖x' - z‖ ^ 2 := h_ratio
    _ ≤ M * ‖x' - z‖ ^ 2 := by gcongr

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_psi_taylor_succ_support_bound_exists (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z : Fin (n + 1) → Fin 4 → ℂ) (k m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x' in 𝓝 z,
      ∀ p, ‖p‖ ≤ 2 * R →
        ‖p‖ ^ k * ‖iteratedFDeriv ℝ (m + 1)
           (⇑(vladimirov_psi_schwartz (n + 1) R hR x' -
              vladimirov_psi_schwartz (n + 1) R hR z -
              vladimirov_deriv_psi_schwartz (n + 1) R hR z (x' - z))) p‖ ≤
          C * ‖x' - z‖ ^ 2 := by
  obtain ⟨M, hM_nonneg, hM⟩ := vladimirov_psi_taylor_succ_unif_bound_exists n R hR z m
  let C := (2 * R) ^ k * M
  use C
  refine ⟨by positivity, ?_⟩
  filter_upwards [hM] with x' hx' p hp
  have h_pk : ‖p‖ ^ k ≤ (2 * R) ^ k := by gcongr
  have h_deriv := hx' p hp
  calc ‖p‖ ^ k * ‖iteratedFDeriv ℝ (m + 1)
         (⇑(vladimirov_psi_schwartz (n + 1) R hR x' -
            vladimirov_psi_schwartz (n + 1) R hR z -
            vladimirov_deriv_psi_schwartz (n + 1) R hR z (x' - z))) p‖
      ≤ (2 * R) ^ k * (M * ‖x' - z‖ ^ 2) := by gcongr
    _ = C * ‖x' - z‖ ^ 2 := by ring

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_psi_taylor_seminorm_succ_pointwise_bound (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z : Fin (n + 1) → Fin 4 → ℂ) (k m : ℕ) :
    ∃ (C : ℝ), 0 ≤ C ∧ ∀ᶠ x' in 𝓝 z,
      ∀ p, ‖p‖ ^ k * ‖iteratedFDeriv ℝ (m + 1)
         (⇑(vladimirov_psi_schwartz (n + 1) R hR x' -
            vladimirov_psi_schwartz (n + 1) R hR z -
            vladimirov_deriv_psi_schwartz (n + 1) R hR z (x' - z))) p‖ ≤
        C * ‖x' - z‖ ^ 2 := by
  obtain ⟨C, hC_nonneg, hC⟩ := vladimirov_psi_taylor_succ_support_bound_exists n R hR z k m
  use C
  refine ⟨hC_nonneg, ?_⟩
  filter_upwards [hC] with x' hx' p
  by_cases hp : ‖p‖ ≤ 2 * R
  · exact hx' p hp
  · have hp_lt : 2 * R < ‖p‖ := not_le.mp hp
    have hz := vladimirov_psi_taylor_succ_zero_of_lt n R hR z x' p m hp_lt
    rw [hz, norm_zero, mul_zero]
    positivity

omit [Fintype ι] [DecidableEq ι] in
lemma schwartz_single_seminorm_quadratic_succ_deriv (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z : Fin (n + 1) → Fin 4 → ℂ) (k m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x' in 𝓝 z,
      (SchwartzMap.seminorm ℝ k (m + 1))
        (vladimirov_psi_schwartz (n + 1) R hR x' -
         vladimirov_psi_schwartz (n + 1) R hR z -
         vladimirov_deriv_psi_schwartz (n + 1) R hR z (x' - z)) ≤ C * ‖x' - z‖ ^ 2 := by
  obtain ⟨C, hC_nonneg, hC⟩ := vladimirov_psi_taylor_seminorm_succ_pointwise_bound n R hR z k m
  use C
  refine ⟨hC_nonneg, ?_⟩
  filter_upwards [hC] with x' hx'
  have h_bound_nonneg : 0 ≤ C * ‖x' - z‖ ^ 2 := mul_nonneg hC_nonneg (sq_nonneg _)
  exact seminorm_succ_le_of_pointwise_bound (n + 1) R hR z x' k m
    (C * ‖x' - z‖ ^ 2) h_bound_nonneg hx'

omit [Fintype ι] [DecidableEq ι] in
lemma schwartz_single_seminorm_quadratic_succ (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z : Fin (n + 1) → Fin 4 → ℂ) (km : ℕ × ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x' in 𝓝 z,
      (schwartzSeminormFamily ℝ (Fin (n + 1) → Fin 4 → ℝ) ℂ km)
        (vladimirov_psi_schwartz (n + 1) R hR x' -
         vladimirov_psi_schwartz (n + 1) R hR z -
         vladimirov_deriv_psi_schwartz (n + 1) R hR z (x' - z)) ≤ C * ‖x' - z‖ ^ 2 := by
  rcases km with ⟨k, m⟩
  change ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x' in 𝓝 z,
    (SchwartzMap.seminorm ℝ k m)
      (vladimirov_psi_schwartz (n + 1) R hR x' -
       vladimirov_psi_schwartz (n + 1) R hR z -
       vladimirov_deriv_psi_schwartz (n + 1) R hR z (x' - z)) ≤ C * ‖x' - z‖ ^ 2
  cases m with
  | zero => exact schwartz_single_seminorm_quadratic_zero_deriv n R hR z k
  | succ m' => exact schwartz_single_seminorm_quadratic_succ_deriv n R hR z k m'

omit [Fintype ι] [DecidableEq ι] in
lemma schwartz_single_seminorm_ratio_bounded_succ (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z : Fin (n + 1) → Fin 4 → ℂ) (km : ℕ × ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x' in 𝓝 z,
      schwartz_single_seminorm_ratio (n + 1) R hR z km x' ≤ C := by
  obtain ⟨C, hC_nonneg, hC⟩ := schwartz_single_seminorm_quadratic_succ n R hR z km
  use C
  refine ⟨hC_nonneg, ?_⟩
  filter_upwards [hC] with x' hx'
  rw [schwartz_single_seminorm_ratio_le_iff _ _ _ _ _ _ _ hC_nonneg]
  exact hx'

omit [Fintype ι] [DecidableEq ι] in
lemma schwartz_single_seminorm_ratio_bounded (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z : Fin n → Fin 4 → ℂ) (km : ℕ × ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x' in 𝓝 z,
      schwartz_single_seminorm_ratio n R hR z km x' ≤ C := by
  cases n with
  | zero =>
    use 0
    refine ⟨le_rfl, ?_⟩
    filter_upwards with x'
    have h_eq : x' = z := Subsingleton.elim x' z
    dsimp [schwartz_single_seminorm_ratio]
    rw [if_pos h_eq]
  | succ m =>
    exact schwartz_single_seminorm_ratio_bounded_succ m R hR z km

omit [Fintype ι] [DecidableEq ι] in
lemma schwartz_single_seminorm_quadratic (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z : Fin n → Fin 4 → ℂ) (km : ℕ × ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x' in 𝓝 z,
      (schwartzSeminormFamily ℝ (Fin n → Fin 4 → ℝ) ℂ km)
        (vladimirov_psi_schwartz n R hR x' -
         vladimirov_psi_schwartz n R hR z -
         vladimirov_deriv_psi_schwartz n R hR z (x' - z)) ≤ C * ‖x' - z‖ ^ 2 := by
  obtain ⟨C, hC_nonneg, hC⟩ := schwartz_single_seminorm_ratio_bounded n R hR z km
  use C
  refine ⟨hC_nonneg, ?_⟩
  filter_upwards [hC] with x' hx'
  have h_le := seminorm_le_single_ratio_mul_sq n R hR z km x'
  calc (schwartzSeminormFamily ℝ (Fin n → Fin 4 → ℝ) ℂ km)
          (vladimirov_psi_schwartz n R hR x' -
           vladimirov_psi_schwartz n R hR z -
           vladimirov_deriv_psi_schwartz n R hR z (x' - z))
      ≤ (schwartz_single_seminorm_ratio n R hR z km x') * ‖x' - z‖ ^ 2 := h_le
    _ ≤ C * ‖x' - z‖ ^ 2 := by gcongr

omit [Fintype ι] [DecidableEq ι] in
lemma schwartz_finset_seminorm_quadratic (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z : Fin n → Fin 4 → ℂ) (s : Finset (ℕ × ℕ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x' in 𝓝 z,
      (s.sup (schwartzSeminormFamily ℝ (Fin n → Fin 4 → ℝ) ℂ))
        (vladimirov_psi_schwartz n R hR x' -
         vladimirov_psi_schwartz n R hR z -
         vladimirov_deriv_psi_schwartz n R hR z (x' - z)) ≤ C * ‖x' - z‖ ^ 2 := by
  induction s using Finset.induction_on with
  | empty =>
    use 0
    refine ⟨le_rfl, ?_⟩
    filter_upwards with x'
    simp only [Finset.sup_empty, zero_mul]
    rfl
  | insert a s' ha ih =>
    obtain ⟨C1, hC1_nonneg, hC1⟩ := schwartz_single_seminorm_quadratic n R hR z a
    obtain ⟨C2, hC2_nonneg, hC2⟩ := ih
    use max C1 C2
    refine ⟨le_max_of_le_left hC1_nonneg, ?_⟩
    filter_upwards [hC1, hC2] with x' hx1 hx2
    rw [Finset.sup_insert]
    simp only [Seminorm.sup_apply]
    apply max_le
    · calc (schwartzSeminormFamily ℝ (Fin n → Fin 4 → ℝ) ℂ a)
            (vladimirov_psi_schwartz n R hR x' -
             vladimirov_psi_schwartz n R hR z -
             vladimirov_deriv_psi_schwartz n R hR z (x' - z))
          ≤ C1 * ‖x' - z‖ ^ 2 := hx1
        _ ≤ max C1 C2 * ‖x' - z‖ ^ 2 := by
          gcongr
          exact le_max_left C1 C2
    · calc (s'.sup (schwartzSeminormFamily ℝ (Fin n → Fin 4 → ℝ) ℂ))
            (vladimirov_psi_schwartz n R hR x' -
             vladimirov_psi_schwartz n R hR z -
             vladimirov_deriv_psi_schwartz n R hR z (x' - z))
          ≤ C2 * ‖x' - z‖ ^ 2 := hx2
        _ ≤ max C1 C2 * ‖x' - z‖ ^ 2 := by
          gcongr
          exact le_max_right C1 C2

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_remainder_ratio_eventually_le (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z : Fin n → Fin 4 → ℂ) (T : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ →L[ℂ] ℂ) :
    ∃ C : ℝ, ∀ᶠ x' in 𝓝 z, vladimirov_remainder_ratio n R hR z T x' ≤ C := by
  obtain ⟨s, C_T, hC_T_pos, hT_bound⟩ := schwartz_clm_bound n T
  obtain ⟨C_s, hC_s_nonneg, hC_s⟩ := schwartz_finset_seminorm_quadratic n R hR z s
  use C_T * C_s
  filter_upwards [hC_s] with x' hx'
  dsimp [vladimirov_remainder_ratio]
  split_ifs with h_eq
  · subst h_eq
    exact mul_nonneg hC_T_pos.le hC_s_nonneg
  · have h_ne : ‖x' - z‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr h_eq)
    have h_sq_pos : 0 < ‖x' - z‖ ^ 2 := by
      exact sq_pos_of_ne_zero (norm_ne_zero_iff.mpr (sub_ne_zero.mpr h_eq))
    have hT_le := hT_bound (vladimirov_psi_schwartz n R hR x' -
        vladimirov_psi_schwartz n R hR z -
        vladimirov_deriv_psi_schwartz n R hR z (x' - z))
    have h_div_le : ‖T (vladimirov_psi_schwartz n R hR x' -
        vladimirov_psi_schwartz n R hR z -
        vladimirov_deriv_psi_schwartz n R hR z (x' - z))‖ ≤
        (C_T * C_s) * ‖x' - z‖ ^ 2 := by
      calc ‖T (vladimirov_psi_schwartz n R hR x' -
               vladimirov_psi_schwartz n R hR z -
               vladimirov_deriv_psi_schwartz n R hR z (x' - z))‖
          ≤ C_T * (s.sup (schwartzSeminormFamily ℝ (Fin n → Fin 4 → ℝ) ℂ))
            (vladimirov_psi_schwartz n R hR x' -
             vladimirov_psi_schwartz n R hR z -
             vladimirov_deriv_psi_schwartz n R hR z (x' - z)) := hT_le
        _ ≤ C_T * (C_s * ‖x' - z‖ ^ 2) := by gcongr
        _ = (C_T * C_s) * ‖x' - z‖ ^ 2 := by ring
    rw [div_le_iff₀ h_sq_pos]
    exact h_div_le

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_psi_schwartz_remainder_quadratic (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z : Fin n → Fin 4 → ℂ) (T : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ →L[ℂ] ℂ) :
    ∃ C : ℝ, ∀ᶠ x' in 𝓝 z,
      ‖T (vladimirov_psi_schwartz n R hR x' -
          vladimirov_psi_schwartz n R hR z -
          vladimirov_deriv_psi_schwartz n R hR z (x' - z))‖ ≤ C * ‖x' - z‖ ^ 2 := by
  obtain ⟨C, hC⟩ := vladimirov_remainder_ratio_eventually_le n R hR z T
  use C
  filter_upwards [hC] with x' hx'
  have h_le := norm_le_ratio_mul_sq n R hR z T x'
  calc ‖T (vladimirov_psi_schwartz n R hR x' -
           vladimirov_psi_schwartz n R hR z -
           vladimirov_deriv_psi_schwartz n R hR z (x' - z))‖
      ≤ (vladimirov_remainder_ratio n R hR z T x') * ‖x' - z‖ ^ 2 := h_le
    _ ≤ C * ‖x' - z‖ ^ 2 := by
      gcongr

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_psi_schwartz_remainder_isLittleO (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z : Fin n → Fin 4 → ℂ) (T : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ →L[ℂ] ℂ) :
    (fun x' => T (vladimirov_psi_schwartz n R hR x' -
                  vladimirov_psi_schwartz n R hR z -
                  vladimirov_deriv_psi_schwartz n R hR z (x' - z))) =o[𝓝 z]
      fun x' => x' - z := by
  obtain ⟨C, hC⟩ := vladimirov_psi_schwartz_remainder_quadratic n R hR z T
  exact isLittleO_of_pow_two z _ C hC

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_hasFDerivAt_schwartz_family (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z : Fin n → Fin 4 → ℂ) (T : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ →L[ℂ] ℂ) :
    HasFDerivAt (fun w => T (vladimirov_psi_schwartz n R hR w))
      (vladimirov_deriv_T_CLM n R hR z T) z := by
  rw [hasFDerivAt_iff_isLittleO]
  have h_rem : (fun x' =>
      T (vladimirov_psi_schwartz n R hR x') - T (vladimirov_psi_schwartz n R hR z) -
        (vladimirov_deriv_T_CLM n R hR z T) (x' - z)) =
      fun x' => T (vladimirov_psi_schwartz n R hR x' - vladimirov_psi_schwartz n R hR z -
        vladimirov_deriv_psi_schwartz n R hR z (x' - z)) := by
    ext x'
    exact vladimirov_fderiv_remainder_linear n R hR z T x'
  rw [h_rem]
  exact vladimirov_psi_schwartz_remainder_isLittleO n R hR z T

omit [Fintype ι] [DecidableEq ι] in
lemma differentiable_schwartz_family_ge_two (n : ℕ) (_hn : ¬ n ≤ 1) (R : ℝ) (hR : 0 < R)
    (z : Fin n → Fin 4 → ℂ) (T : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ →L[ℂ] ℂ) :
    DifferentiableAt ℂ (fun w => T (vladimirov_psi_schwartz n R hR w)) z :=
  (vladimirov_hasFDerivAt_schwartz_family n R hR z T).differentiableAt

omit [Fintype ι] [DecidableEq ι] in
lemma slice_analytic_1d {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : E → ℂ) (z v : E)
    (hf : Differentiable ℂ (fun t : ℂ => f (z + t • v))) :
    AnalyticAt ℂ (fun t : ℂ => f (z + t • v)) 0 :=
  hf.analyticAt 0

omit [Fintype ι] [DecidableEq ι] in
lemma slice_differentiable_schwartz_family (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z v : Fin n → Fin 4 → ℂ) (T : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ →L[ℂ] ℂ)
    (h_diff : ∀ w, DifferentiableAt ℂ (fun w => T (vladimirov_psi_schwartz n R hR w)) w) :
    Differentiable ℂ
      (fun t : ℂ => (fun w => T (vladimirov_psi_schwartz n R hR w)) (z + t • v)) := by
  let F := fun w => T (vladimirov_psi_schwartz n R hR w)
  have hF : Differentiable ℂ F := fun w => h_diff w
  let L : ℂ → (Fin n → Fin 4 → ℂ) := fun t => z + t • v
  have hL : Differentiable ℂ L := by
    apply Differentiable.add
    · exact differentiable_const z
    · exact differentiable_id.smul_const v
  exact hF.comp hL

omit [Fintype ι] [DecidableEq ι] in
lemma slice_analytic_schwartz_family (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z v : Fin n → Fin 4 → ℂ) (T : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ →L[ℂ] ℂ)
    (h_diff : ∀ w, DifferentiableAt ℂ (fun w => T (vladimirov_psi_schwartz n R hR w)) w) :
    AnalyticAt ℂ (fun t : ℂ => (fun w => T (vladimirov_psi_schwartz n R hR w)) (z + t • v)) 0 :=
  slice_analytic_1d (fun w => T (vladimirov_psi_schwartz n R hR w)) z v
    (slice_differentiable_schwartz_family n R hR z v T h_diff)

omit [Fintype ι] [DecidableEq ι] in
lemma slice_fun_zero_dir {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : E → ℂ) (z : E) :
    (fun t : ℂ => f (z + t • (0 : E))) = fun _ => f z := by
  ext t
  simp only [smul_zero, add_zero]

omit [Fintype ι] [DecidableEq ι] in
lemma slice_analytic_zero_dir {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : E → ℂ) (z : E) :
    AnalyticAt ℂ (fun t : ℂ => f (z + t • (0 : E))) 0 := by
  rw [slice_fun_zero_dir]
  exact analyticAt_const

omit [Fintype ι] [DecidableEq ι] in
lemma differentiableAt_slice_of_analytic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : E → ℂ) (z v : E)
    (h_slice : AnalyticAt ℂ (fun t : ℂ => f (z + t • v)) 0) :
    DifferentiableAt ℂ (fun t : ℂ => f (z + t • v)) 0 :=
  h_slice.differentiableAt

section VladimirovMultilinearAnalytic
omit [Fintype ι] [DecidableEq ι]

noncomputable def vladimirov_iter_psi (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z h : Fin n → Fin 4 → ℂ) (k : ℕ) (p : Fin n → Fin 4 → ℝ) : ℂ :=
  (vladimirov_phase_CLM n h p) ^ k * vladimirov_psi n R hR z p

lemma vladimirov_iter_psi_contDiff (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z h : Fin n → Fin 4 → ℂ) (k : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p => vladimirov_iter_psi n R hR z h k p) := by
  change ContDiff ℝ (⊤ : ℕ∞) (fun p => (vladimirov_phase_CLM n h p) ^ k * vladimirov_psi n R hR z p)
  apply ContDiff.mul
  · exact (vladimirov_phase_CLM n h).contDiff.pow k
  · exact vladimirov_psi_contDiff n R hR z

lemma vladimirov_iter_psi_hasCompactSupport (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z h : Fin n → Fin 4 → ℂ) (k : ℕ) :
    HasCompactSupport (fun p => vladimirov_iter_psi n R hR z h k p) := by
  change HasCompactSupport (fun p => (vladimirov_phase_CLM n h p) ^ k * vladimirov_psi n R hR z p)
  have h_supp : HasCompactSupport (vladimirov_psi n R hR z) :=
    vladimirov_psi_hasCompactSupport n R hR z
  exact h_supp.mul_left

noncomputable def vladimirov_iter_psi_schwartz (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z h : Fin n → Fin 4 → ℂ) (k : ℕ) :
    SchwartzMap (Fin n → Fin 4 → ℝ) ℂ :=
  (vladimirov_iter_psi_hasCompactSupport n R hR z h k).toSchwartzMap
    (vladimirov_iter_psi_contDiff n R hR z h k)

lemma vladimirov_iter_psi_smul_eval (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z h : Fin n → Fin 4 → ℂ) (c : ℂ) (k : ℕ) (p : Fin n → Fin 4 → ℝ) :
    vladimirov_iter_psi n R hR z (c • h) k p =
      c ^ k * vladimirov_iter_psi n R hR z h k p := by
  dsimp [vladimirov_iter_psi]
  rw [vladimirov_phase_clm_eq_phase_z_clm n (c • h),
      vladimirov_phase_clm_eq_phase_z_clm n h]
  rw [vladimirov_phase_z_CLM_smul]
  dsimp [HSMul.hSMul, SMul.smul]
  rw [mul_pow]
  ring

lemma vladimirov_iter_psi_schwartz_smul (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z h : Fin n → Fin 4 → ℂ) (c : ℂ) (k : ℕ) :
    vladimirov_iter_psi_schwartz n R hR z (c • h) k =
      c ^ k • vladimirov_iter_psi_schwartz n R hR z h k := by
  ext p
  exact vladimirov_iter_psi_smul_eval n R hR z h c k p

noncomputable def vladimirov_taylor_coeff (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z : Fin n → Fin 4 → ℂ) (T : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ →L[ℂ] ℂ)
    (k : ℕ) (h : Fin n → Fin 4 → ℂ) : ℂ :=
  ((Nat.factorial k : ℝ) : ℂ)⁻¹ * T (vladimirov_iter_psi_schwartz n R hR z h k)

lemma vladimirov_taylor_coeff_smul (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z : Fin n → Fin 4 → ℂ) (T : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ →L[ℂ] ℂ)
    (k : ℕ) (c : ℂ) (h : Fin n → Fin 4 → ℂ) :
    vladimirov_taylor_coeff n R hR z T k (c • h) =
      c ^ k * vladimirov_taylor_coeff n R hR z T k h := by
  dsimp [vladimirov_taylor_coeff]
  rw [vladimirov_iter_psi_schwartz_smul]
  rw [map_smul, smul_eq_mul]
  ring

noncomputable def vladimirov_multilinear_psi (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z : Fin n → Fin 4 → ℂ) (k : ℕ) (h : Fin k → (Fin n → Fin 4 → ℂ))
    (p : Fin n → Fin 4 → ℝ) : ℂ :=
  (∏ j : Fin k, vladimirov_phase_CLM n (h j) p) * vladimirov_psi n R hR z p

lemma vladimirov_multilinear_psi_diag (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z : Fin n → Fin 4 → ℂ) (k : ℕ) (v : Fin n → Fin 4 → ℂ) (p : Fin n → Fin 4 → ℝ) :
    vladimirov_multilinear_psi n R hR z k (fun _ => v) p =
      vladimirov_iter_psi n R hR z v k p := by
  dsimp [vladimirov_multilinear_psi, vladimirov_iter_psi]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

lemma vladimirov_multilinear_psi_zero (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z : Fin n → Fin 4 → ℂ) (j : Fin 0 → (Fin n → Fin 4 → ℂ))
    (p : Fin n → Fin 4 → ℝ) :
    vladimirov_multilinear_psi n R hR z 0 j p = vladimirov_psi n R hR z p := by
  dsimp [vladimirov_multilinear_psi]
  rw [Fin.prod_univ_zero, one_mul]

lemma vladimirov_multilinear_psi_succ (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z : Fin n → Fin 4 → ℂ) (k : ℕ) (j : Fin (k + 1) → (Fin n → Fin 4 → ℂ))
    (p : Fin n → Fin 4 → ℝ) :
    vladimirov_multilinear_psi n R hR z (k + 1) j p =
      vladimirov_phase_CLM n (j 0) p *
        vladimirov_multilinear_psi n R hR z k (fun m => j (Fin.succ m)) p := by
  dsimp [vladimirov_multilinear_psi]
  rw [Fin.prod_univ_succ]
  ring

lemma vladimirov_multilinear_psi_contDiff (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z : Fin n → Fin 4 → ℂ) (k : ℕ) (h : Fin k → (Fin n → Fin 4 → ℂ)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p => vladimirov_multilinear_psi n R hR z k h p) := by
  change ContDiff ℝ (⊤ : ℕ∞) (fun p => (∏ j : Fin k, vladimirov_phase_CLM n (h j) p) *
    vladimirov_psi n R hR z p)
  apply ContDiff.mul
  · apply contDiff_prod
    intro j _
    exact (vladimirov_phase_CLM n (h j)).contDiff
  · exact vladimirov_psi_contDiff n R hR z

lemma vladimirov_multilinear_psi_hasCompactSupport (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z : Fin n → Fin 4 → ℂ) (k : ℕ) (h : Fin k → (Fin n → Fin 4 → ℂ)) :
    HasCompactSupport (fun p => vladimirov_multilinear_psi n R hR z k h p) := by
  change HasCompactSupport (fun p => (∏ j : Fin k, vladimirov_phase_CLM n (h j) p) *
    vladimirov_psi n R hR z p)
  have h_supp : HasCompactSupport (vladimirov_psi n R hR z) :=
    vladimirov_psi_hasCompactSupport n R hR z
  exact h_supp.mul_left

noncomputable def vladimirov_multilinear_psi_schwartz (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z : Fin n → Fin 4 → ℂ) (k : ℕ) (h : Fin k → (Fin n → Fin 4 → ℂ)) :
    SchwartzMap (Fin n → Fin 4 → ℝ) ℂ :=
  (vladimirov_multilinear_psi_hasCompactSupport n R hR z k h).toSchwartzMap
    (vladimirov_multilinear_psi_contDiff n R hR z k h)

lemma vladimirov_multilinear_psi_schwartz_diag (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z : Fin n → Fin 4 → ℂ) (k : ℕ) (v : Fin n → Fin 4 → ℂ) :
    vladimirov_multilinear_psi_schwartz n R hR z k (fun _ => v) =
      vladimirov_iter_psi_schwartz n R hR z v k := by
  ext p
  exact vladimirov_multilinear_psi_diag n R hR z k v p

noncomputable def vladimirov_phase_multilinear (n : ℕ) (p : Fin n → Fin 4 → ℝ) (k : ℕ) :
    ContinuousMultilinearMap ℂ (fun _ : Fin k => (Fin n → Fin 4 → ℂ)) ℂ :=
  (ContinuousMultilinearMap.mkPiAlgebraFin ℂ k ℂ).compContinuousLinearMap
    (fun _ => vladimirov_phase_z_CLM n p)

lemma vladimirov_phase_multilinear_diag (n : ℕ) (p : Fin n → Fin 4 → ℝ) (k : ℕ)
    (v : Fin n → Fin 4 → ℂ) :
    vladimirov_phase_multilinear n p k (fun _ => v) = (vladimirov_phase_CLM n v p) ^ k := by
  dsimp [vladimirov_phase_multilinear]
  simp only [vladimirov_phase_clm_eq_phase_z_clm]
  rw [List.ofFn_const, List.prod_replicate]

lemma vladimirov_phase_multilinear_norm_le (n : ℕ) (p : Fin n → Fin 4 → ℝ) (k : ℕ) :
    ‖vladimirov_phase_multilinear n p k‖ ≤ ‖vladimirov_phase_z_CLM n p‖ ^ k := by
  dsimp [vladimirov_phase_multilinear]
  have h_le := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (ContinuousMultilinearMap.mkPiAlgebraFin ℂ k ℂ) (fun _ => vladimirov_phase_z_CLM n p)
  have h_prod : ∏ _i : Fin k, ‖vladimirov_phase_z_CLM n p‖ = ‖vladimirov_phase_z_CLM n p‖ ^ k := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have h_mk : ‖ContinuousMultilinearMap.mkPiAlgebraFin ℂ k ℂ‖ ≤ 1 := by
    cases k with
    | zero =>
      rw [ContinuousMultilinearMap.norm_mkPiAlgebraFin_zero]
      exact norm_one.le
    | succ m =>
      exact ContinuousMultilinearMap.norm_mkPiAlgebraFin_succ_le
  calc ‖(ContinuousMultilinearMap.mkPiAlgebraFin ℂ k ℂ).compContinuousLinearMap
          (fun _ => vladimirov_phase_z_CLM n p)‖
      ≤ ‖ContinuousMultilinearMap.mkPiAlgebraFin ℂ k ℂ‖ *
          ∏ _i : Fin k, ‖vladimirov_phase_z_CLM n p‖ := h_le
    _ = ‖ContinuousMultilinearMap.mkPiAlgebraFin ℂ k ℂ‖ *
        ‖vladimirov_phase_z_CLM n p‖ ^ k := by rw [h_prod]
    _ ≤ 1 * ‖vladimirov_phase_z_CLM n p‖ ^ k := by gcongr
    _ = ‖vladimirov_phase_z_CLM n p‖ ^ k := one_mul _

noncomputable def vladimirov_proj (n : ℕ) (i : Fin n × Fin 4) :
    (Fin n → Fin 4 → ℂ) →L[ℂ] ℂ :=
  (ContinuousLinearMap.proj (R := ℂ) (ι := Fin 4) (φ := fun _ => ℂ) i.2).comp
    (ContinuousLinearMap.proj (R := ℂ) (ι := Fin n) (φ := fun _ => Fin 4 → ℂ) i.1)

lemma vladimirov_proj_apply (n : ℕ) (i : Fin n × Fin 4) (w : Fin n → Fin 4 → ℂ) :
    vladimirov_proj n i w = w i.1 i.2 := rfl

lemma vladimirov_proj_norm_le (n : ℕ) (i : Fin n × Fin 4) :
    ‖vladimirov_proj n i‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => ?_
  simp only [one_mul, vladimirov_proj_apply]
  exact (norm_le_pi_norm (w i.1) i.2).trans (norm_le_pi_norm w i.1)

noncomputable def vladimirov_monomial_multilinear (n : ℕ) (k : ℕ)
    (j : Fin k → Fin n × Fin 4) :
    ContinuousMultilinearMap ℂ (fun _ : Fin k => (Fin n → Fin 4 → ℂ)) ℂ :=
  (ContinuousMultilinearMap.mkPiAlgebraFin ℂ k ℂ).compContinuousLinearMap
    (fun m => vladimirov_proj n (j m))

lemma vladimirov_monomial_multilinear_diag (n : ℕ) (k : ℕ)
    (j : Fin k → Fin n × Fin 4) (w : Fin n → Fin 4 → ℂ) :
    vladimirov_monomial_multilinear n k j (fun _ => w) =
      ∏ m : Fin k, w (j m).1 (j m).2 := by
  dsimp [vladimirov_monomial_multilinear]
  rw [List.prod_ofFn]
  rfl

lemma vladimirov_monomial_multilinear_norm_le (n : ℕ) (k : ℕ)
    (j : Fin k → Fin n × Fin 4) :
    ‖vladimirov_monomial_multilinear n k j‖ ≤ 1 := by
  dsimp [vladimirov_monomial_multilinear]
  have h_le := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (ContinuousMultilinearMap.mkPiAlgebraFin ℂ k ℂ) (fun m => vladimirov_proj n (j m))
  have h_mk : ‖ContinuousMultilinearMap.mkPiAlgebraFin ℂ k ℂ‖ ≤ 1 := by
    cases k with
    | zero =>
      rw [ContinuousMultilinearMap.norm_mkPiAlgebraFin_zero]
      exact norm_one.le
    | succ m =>
      exact ContinuousMultilinearMap.norm_mkPiAlgebraFin_succ_le
  have h_prod : ∏ m : Fin k, ‖vladimirov_proj n (j m)‖ ≤ 1 := by
    refine Finset.prod_le_one (fun (m : Fin k) _ => norm_nonneg (vladimirov_proj n (j m))) ?_
    intro m _
    exact vladimirov_proj_norm_le n (j m)
  calc ‖(ContinuousMultilinearMap.mkPiAlgebraFin ℂ k ℂ).compContinuousLinearMap
          (fun m => vladimirov_proj n (j m))‖
      ≤ ‖ContinuousMultilinearMap.mkPiAlgebraFin ℂ k ℂ‖ *
          ∏ m : Fin k, ‖vladimirov_proj n (j m)‖ := h_le
    _ ≤ 1 * 1 := by gcongr
    _ = 1 := mul_one 1

noncomputable def vladimirov_basis (n : ℕ) (i : Fin n × Fin 4) : Fin n → Fin 4 → ℂ :=
  fun a mu => if a = i.1 ∧ mu = i.2 then (1 : ℂ) else 0

lemma vladimirov_basis_norm_le (n : ℕ) (i : Fin n × Fin 4) :
    ‖vladimirov_basis n i‖ ≤ 1 := by
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intro a
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intro mu
  dsimp [vladimirov_basis]
  split_ifs with h
  · exact norm_one.le
  · simp only [norm_zero, zero_le_one]

lemma vladimirov_phase_basis_support_bound_all (n : ℕ) (R : ℝ) (hR : 0 < R) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (i : Fin (n + 1) × Fin 4) p,
      p ∈ Function.support (vladimirovCutoffBump (n + 1) R hR) →
      ‖vladimirov_phase_CLM (n + 1) (vladimirov_basis (n + 1) i) p‖ ≤ B := by
  obtain ⟨B, hB_nonneg, hB⟩ := vladimirov_phase_z_clm_support_bound n R hR
  use B
  refine ⟨hB_nonneg, ?_⟩
  intro i p hp
  rw [vladimirov_phase_clm_eq_phase_z_clm]
  have h_le := (vladimirov_phase_z_CLM (n + 1) p).le_opNorm (vladimirov_basis (n + 1) i)
  have h_basis := vladimirov_basis_norm_le (n + 1) i
  have h_p := hB p hp
  calc ‖(vladimirov_phase_z_CLM (n + 1) p) (vladimirov_basis (n + 1) i)‖
      ≤ ‖vladimirov_phase_z_CLM (n + 1) p‖ * ‖vladimirov_basis (n + 1) i‖ := h_le
    _ ≤ B * 1 := by gcongr
    _ = B := mul_one B

lemma vladimirov_phase_basis_prod_bound (n : ℕ) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (j : Fin k → Fin (n + 1) × Fin 4) (p : Fin (n + 1) → Fin 4 → ℝ)
    (hp : p ∈ Function.support (vladimirovCutoffBump (n + 1) R hR)) (B : ℝ)
    (hB : ∀ (i : Fin (n + 1) × Fin 4) p,
      p ∈ Function.support (vladimirovCutoffBump (n + 1) R hR) →
      ‖vladimirov_phase_CLM (n + 1) (vladimirov_basis (n + 1) i) p‖ ≤ B) :
    ‖∏ m : Fin k, vladimirov_phase_CLM (n + 1) (vladimirov_basis (n + 1) (j m)) p‖ ≤ B ^ k := by
  rw [norm_prod]
  have h_prod : (∏ m : Fin k, ‖vladimirov_phase_CLM (n + 1) (vladimirov_basis (n + 1) (j m)) p‖) ≤
      ∏ _m : Fin k, B := by
    refine Finset.prod_le_prod (fun m _ => norm_nonneg _) (fun m _ => hB (j m) p hp)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h_prod
  exact h_prod

lemma vladimirov_multilinear_psi_pointwise_bound (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z : Fin (n + 1) → Fin 4 → ℂ) (k : ℕ) (j : Fin k → Fin (n + 1) × Fin 4)
    (p : Fin (n + 1) → Fin 4 → ℝ) (B : ℝ) (hB_nonneg : 0 ≤ B)
    (hB : ∀ (i : Fin (n + 1) × Fin 4) p,
      p ∈ Function.support (vladimirovCutoffBump (n + 1) R hR) →
      ‖vladimirov_phase_CLM (n + 1) (vladimirov_basis (n + 1) i) p‖ ≤ B) :
    ‖vladimirov_multilinear_psi (n + 1) R hR z k (fun m => vladimirov_basis (n + 1) (j m)) p‖ ≤
      B ^ k * Real.exp (‖vladimirov_phase_CLM (n + 1) z‖ * (2 * R)) := by
  dsimp [vladimirov_multilinear_psi]
  rw [norm_mul]
  by_cases hp : p ∈ Function.support (vladimirovCutoffBump (n + 1) R hR)
  · have h_prod := vladimirov_phase_basis_prod_bound n R hR k j p hp B hB
    have h_psi := vladimirov_psi_bound_on_support n R hR z p hp
    have hB_pow : 0 ≤ B ^ k := pow_nonneg hB_nonneg k
    have h_exp_nonneg : 0 ≤ Real.exp (‖vladimirov_phase_CLM (n + 1) z‖ * (2 * R)) :=
      (Real.exp_pos _).le
    exact mul_le_mul h_prod h_psi (norm_nonneg _) hB_pow
  · have h_zero := vladimirov_psi_eq_zero_of_not_mem_support (n + 1) R hR z p hp
    rw [h_zero, norm_zero, mul_zero]
    exact mul_nonneg (pow_nonneg hB_nonneg k) (Real.exp_pos _).le

lemma vladimirov_basis_expansion (n : ℕ) (w : Fin n → Fin 4 → ℂ) :
    w = ∑ i : Fin n × Fin 4, w i.1 i.2 • vladimirov_basis n i := by
  ext a mu
  simp only [vladimirov_basis, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have h_single :
      (∑ i : Fin n × Fin 4, w i.1 i.2 * if i.1 = a ∧ i.2 = mu then 1 else 0) = w a mu := by
    rw [Finset.sum_eq_single (a, mu)]
    · simp only [and_self, ↓reduceIte, mul_one]
    · intro (b, ν) _ hne
      have : ¬(b = a ∧ ν = mu) := fun h => hne (Prod.ext h.1 h.2)
      simp only [this, ↓reduceIte, mul_zero]
    · intro h
      exact False.elim (h (Finset.mem_univ _))
  have h_eq : (∑ i : Fin n × Fin 4, w i.1 i.2 * if a = i.1 ∧ mu = i.2 then 1 else 0) =
              (∑ i : Fin n × Fin 4, w i.1 i.2 * if i.1 = a ∧ i.2 = mu then 1 else 0) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    by_cases h : (a = i.1 ∧ mu = i.2)
    · rw [if_pos h, if_pos ⟨h.1.symm, h.2.symm⟩]
    · have : ¬(i.1 = a ∧ i.2 = mu) := fun h2 => h ⟨h2.1.symm, h2.2.symm⟩
      rw [if_neg h, if_neg this]
  rw [h_eq, h_single]

lemma vladimirov_phase_basis_expansion (n : ℕ) (p : Fin n → Fin 4 → ℝ)
    (w : Fin n → Fin 4 → ℂ) :
    vladimirov_phase_z_CLM n p w =
      ∑ i : Fin n × Fin 4, w i.1 i.2 * vladimirov_phase_z_CLM n p (vladimirov_basis n i) := by
  conv_lhs => rw [vladimirov_basis_expansion n w]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ContinuousLinearMap.map_smul, smul_eq_mul]

lemma vladimirov_phase_pow_expansion (n : ℕ) (p : Fin n → Fin 4 → ℝ)
    (w : Fin n → Fin 4 → ℂ) (k : ℕ) :
    (vladimirov_phase_z_CLM n p w) ^ k =
      ∑ j : Fin k → Fin n × Fin 4,
        (∏ m : Fin k, w (j m).1 (j m).2) *
        (∏ m : Fin k, vladimirov_phase_z_CLM n p (vladimirov_basis n (j m))) := by
  rw [vladimirov_phase_basis_expansion n p w]
  rw [Fintype.sum_pow]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.prod_mul_distrib]

noncomputable def vladimirov_basis_coeff (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z : Fin n → Fin 4 → ℂ) (T : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ →L[ℂ] ℂ)
    (k : ℕ) (j : Fin k → Fin n × Fin 4) : ℂ :=
  ((Nat.factorial k : ℝ) : ℂ)⁻¹ *
    T (vladimirov_multilinear_psi_schwartz n R hR z k (fun m => vladimirov_basis n (j m)))

noncomputable def vladimirov_taylor_multilinear (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z : Fin n → Fin 4 → ℂ) (T : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ →L[ℂ] ℂ)
    (k : ℕ) : ContinuousMultilinearMap ℂ (fun _ : Fin k => (Fin n → Fin 4 → ℂ)) ℂ :=
  ∑ j : Fin k → Fin n × Fin 4,
    vladimirov_basis_coeff n R hR z T k j • vladimirov_monomial_multilinear n k j

noncomputable def schwartz_eval (n : ℕ) (p : Fin n → Fin 4 → ℝ) :
    SchwartzMap (Fin n → Fin 4 → ℝ) ℂ →ₗ[ℂ] ℂ where
  toFun f := f p
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma vladimirov_basis_sum_schwartz_eq (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z : Fin n → Fin 4 → ℂ) (k : ℕ) (w : Fin n → Fin 4 → ℂ) :
    (∑ j : Fin k → Fin n × Fin 4,
      (∏ m : Fin k, w (j m).1 (j m).2) •
        vladimirov_multilinear_psi_schwartz n R hR z k (fun m => vladimirov_basis n (j m))) =
      vladimirov_iter_psi_schwartz n R hR z w k := by
  ext p
  have h_eval := map_sum (schwartz_eval n p)
    (fun j : Fin k → Fin n × Fin 4 =>
      (∏ m : Fin k, w (j m).1 (j m).2) •
        vladimirov_multilinear_psi_schwartz n R hR z k (fun m => vladimirov_basis n (j m)))
    Finset.univ
  change (schwartz_eval n p) (∑ j, _) = _
  rw [h_eval]
  dsimp [schwartz_eval]
  have h_term : (∑ j : Fin k → Fin n × Fin 4,
      ((∏ m : Fin k, w (j m).1 (j m).2) •
        vladimirov_multilinear_psi_schwartz n R hR z k (fun m => vladimirov_basis n (j m))) p) =
      ∑ j : Fin k → Fin n × Fin 4,
        (∏ m : Fin k, w (j m).1 (j m).2) *
          ((∏ m : Fin k, vladimirov_phase_CLM n (vladimirov_basis n (j m)) p) *
            vladimirov_psi n R hR z p) := by
    refine Finset.sum_congr rfl fun j _ => rfl
  rw [h_term]
  dsimp [vladimirov_iter_psi_schwartz, HasCompactSupport.toSchwartzMap, vladimirov_iter_psi]
  simp only [vladimirov_phase_clm_eq_phase_z_clm]
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul]
  congr 1
  exact (vladimirov_phase_pow_expansion n p w k).symm

lemma vladimirov_taylor_multilinear_diag (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z : Fin n → Fin 4 → ℂ) (T : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ →L[ℂ] ℂ)
    (k : ℕ) (w : Fin n → Fin 4 → ℂ) :
    vladimirov_taylor_multilinear n R hR z T k (fun _ => w) =
      vladimirov_taylor_coeff n R hR z T k w := by
  dsimp [vladimirov_taylor_multilinear, vladimirov_basis_coeff, vladimirov_taylor_coeff]
  simp only [_root_.sum_apply, _root_.smul_apply, smul_eq_mul,
    vladimirov_monomial_multilinear_diag]
  have h_pull : (∑ j : Fin k → Fin n × Fin 4,
      ((k.factorial : ℂ)⁻¹ *
        T (vladimirov_multilinear_psi_schwartz n R hR z k (fun m => vladimirov_basis n (j m)))) *
        ∏ m : Fin k, w (j m).1 (j m).2) =
      (k.factorial : ℂ)⁻¹ *
        ∑ j : Fin k → Fin n × Fin 4,
          (∏ m : Fin k, w (j m).1 (j m).2) *
            T (vladimirov_multilinear_psi_schwartz n R hR z k
              (fun m => vladimirov_basis n (j m))) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => by ring
  rw [h_pull]
  congr 1
  have h_map : (∑ j : Fin k → Fin n × Fin 4,
      (∏ m : Fin k, w (j m).1 (j m).2) *
        T (vladimirov_multilinear_psi_schwartz n R hR z k (fun m => vladimirov_basis n (j m)))) =
      T (∑ j : Fin k → Fin n × Fin 4,
        (∏ m : Fin k, w (j m).1 (j m).2) •
          vladimirov_multilinear_psi_schwartz n R hR z k (fun m => vladimirov_basis n (j m))) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ContinuousLinearMap.map_smul, smul_eq_mul]
  rw [h_map, vladimirov_basis_sum_schwartz_eq]

lemma vladimirov_taylor_multilinear_norm_le (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z : Fin n → Fin 4 → ℂ) (T : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ →L[ℂ] ℂ) (k : ℕ) :
    ‖vladimirov_taylor_multilinear n R hR z T k‖ ≤
      ∑ j : Fin k → Fin n × Fin 4, ‖vladimirov_basis_coeff n R hR z T k j‖ := by
  dsimp [vladimirov_taylor_multilinear]
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro j _
  rw [norm_smul]
  have h_le := vladimirov_monomial_multilinear_norm_le n k j
  exact mul_le_of_le_one_right (norm_nonneg _) h_le

lemma vladimirov_basis_coeff_norm (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z : Fin n → Fin 4 → ℂ) (T : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ →L[ℂ] ℂ)
    (k : ℕ) (j : Fin k → Fin n × Fin 4) :
    ‖vladimirov_basis_coeff n R hR z T k j‖ =
      (k.factorial : ℝ)⁻¹ *
        ‖T (vladimirov_multilinear_psi_schwartz n R hR z k
          (fun m => vladimirov_basis n (j m)))‖ := by
  dsimp [vladimirov_basis_coeff]
  rw [norm_mul, norm_inv, norm_natCast]

noncomputable def vladimirov_formal_series (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z : Fin n → Fin 4 → ℂ) (T : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ →L[ℂ] ℂ) :
    FormalMultilinearSeries ℂ (Fin n → Fin 4 → ℂ) ℂ :=
  fun k => vladimirov_taylor_multilinear n R hR z T k

lemma vladimirov_formal_series_apply (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z : Fin n → Fin 4 → ℂ) (T : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ →L[ℂ] ℂ)
    (k : ℕ) (w : Fin n → Fin 4 → ℂ) :
    (vladimirov_formal_series n R hR z T) k (fun _ => w) =
      vladimirov_taylor_coeff n R hR z T k w :=
  vladimirov_taylor_multilinear_diag n R hR z T k w

lemma vladimirov_multilinear_psi_schwartz_single_bound_zero (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z : Fin (n + 1) → Fin 4 → ℂ) (l : ℕ) :
    ∃ C M : ℝ, 0 ≤ C ∧ 0 ≤ M ∧ ∀ (k : ℕ) (j : Fin k → Fin (n + 1) × Fin 4),
      (schwartzSeminormFamily ℝ (Fin (n + 1) → Fin 4 → ℝ) ℂ (l, 0))
        (vladimirov_multilinear_psi_schwartz (n + 1) R hR z k
          (fun m => vladimirov_basis (n + 1) (j m))) ≤ C * M ^ k := by
  obtain ⟨B, hB_nonneg, hB⟩ := vladimirov_phase_basis_support_bound_all n R hR
  let C := (2 * R) ^ l * Real.exp (‖vladimirov_phase_CLM (n + 1) z‖ * (2 * R))
  use C, B
  refine ⟨by positivity, hB_nonneg, ?_⟩
  intro k j
  change (SchwartzMap.seminorm ℝ l 0)
    (vladimirov_multilinear_psi_schwartz (n + 1) R hR z k
      (fun m => vladimirov_basis (n + 1) (j m))) ≤ C * B ^ k
  refine SchwartzMap.seminorm_le_bound ℝ l 0 _ (by positivity) ?_
  intro p
  rw [norm_iteratedFDeriv_zero]
  change ‖p‖ ^ l *
    ‖vladimirov_multilinear_psi (n + 1) R hR z k (fun m => vladimirov_basis (n + 1) (j m)) p‖ ≤
    C * B ^ k
  by_cases hp : p ∈ Function.support (vladimirovCutoffBump (n + 1) R hR)
  · have h_norm_p := vladimirov_support_norm_lt n R hR p hp
    have h_pl : ‖p‖ ^ l ≤ (2 * R) ^ l := by gcongr
    have h_psi := vladimirov_multilinear_psi_pointwise_bound n R hR z k j p B hB_nonneg hB
    calc ‖p‖ ^ l *
          ‖vladimirov_multilinear_psi (n + 1) R hR z k
            (fun m => vladimirov_basis (n + 1) (j m)) p‖
        ≤ (2 * R) ^ l * (B ^ k * Real.exp (‖vladimirov_phase_CLM (n + 1) z‖ * (2 * R))) := by gcongr
      _ = C * B ^ k := by ring
  · have h_zero := vladimirov_psi_eq_zero_of_not_mem_support (n + 1) R hR z p hp
    have h_multi_zero :
        vladimirov_multilinear_psi (n + 1) R hR z k
          (fun m => vladimirov_basis (n + 1) (j m)) p = 0 := by
      dsimp [vladimirov_multilinear_psi]
      rw [h_zero, mul_zero]
    rw [h_multi_zero, norm_zero, mul_zero]
    positivity

lemma factorial_inv_mul_self (i : ℕ) (hi : 1 ≤ i) :
    (i.factorial : ℝ)⁻¹ * (i : ℝ) = ((i - 1).factorial : ℝ)⁻¹ := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
  rw [Nat.factorial_succ, Nat.cast_mul]
  have h_ne : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  rw [_root_.mul_inv_rev]
  calc (k.factorial : ℝ)⁻¹ * ((k + 1 : ℕ) : ℝ)⁻¹ * ((k + 1 : ℕ) : ℝ)
      = (k.factorial : ℝ)⁻¹ * (((k + 1 : ℕ) : ℝ)⁻¹ * ((k + 1 : ℕ) : ℝ)) := by ring
    _ = (k.factorial : ℝ)⁻¹ * 1 := by rw [inv_mul_cancel₀ h_ne]
    _ = (k.factorial : ℝ)⁻¹ := mul_one _
    _ = ((k + 1 - 1).factorial : ℝ)⁻¹ := rfl

lemma taylor_sum_bound (m : ℕ) (a : ℕ → ℝ) (ha : ∀ i, 0 ≤ a i) (B0 B1 : ℝ)
    (_hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1) :
    (∑ i ∈ Finset.range (m + 1),
      (i.factorial : ℝ)⁻¹ * (B0 * a i + (i : ℝ) * B1 * (if 1 ≤ i then a (i - 1) else 0))) ≤
      (B0 + B1) * (∑ i ∈ Finset.range (m + 1), (i.factorial : ℝ)⁻¹ * a i) := by
  have h_split : ∀ i,
      (i.factorial : ℝ)⁻¹ * (B0 * a i + (i : ℝ) * B1 * (if 1 ≤ i then a (i - 1) else 0)) =
        B0 * ((i.factorial : ℝ)⁻¹ * a i) +
        B1 * ((i.factorial : ℝ)⁻¹ * (i : ℝ) * (if 1 ≤ i then a (i - 1) else 0)) := by
    intro i; ring
  simp_rw [h_split]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have h_term2 :
      (∑ i ∈ Finset.range (m + 1),
        (i.factorial : ℝ)⁻¹ * (i : ℝ) * (if 1 ≤ i then a (i - 1) else 0)) ≤
      ∑ i ∈ Finset.range (m + 1), (i.factorial : ℝ)⁻¹ * a i := by
    cases m with
    | zero =>
      simpa using ha 0
    | succ m' =>
      rw [Finset.sum_range_succ']
      simp only [Nat.cast_zero, mul_zero, zero_mul, add_zero]
      have h_step : ∀ j ∈ Finset.range (m' + 1),
          ((j + 1).factorial : ℝ)⁻¹ * ((j + 1 : ℕ) : ℝ) *
            (if 1 ≤ j + 1 then a (j + 1 - 1) else 0) =
          (j.factorial : ℝ)⁻¹ * a j := by
        intro j _
        have h1 : 1 ≤ j + 1 := by omega
        rw [if_pos h1]
        have h_sub : j + 1 - 1 = j := rfl
        rw [h_sub]
        have h_fac := factorial_inv_mul_self (j + 1) h1
        have h_sub' : (j + 1 - 1) = j := rfl
        rw [h_sub'] at h_fac
        calc ((j + 1).factorial : ℝ)⁻¹ * ((j + 1 : ℕ) : ℝ) * a j
            = (((j + 1).factorial : ℝ)⁻¹ * ((j + 1 : ℕ) : ℝ)) * a j := by ring
          _ = (j.factorial : ℝ)⁻¹ * a j := by rw [h_fac]
      rw [Finset.sum_congr rfl h_step]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.le_succ (m' + 1)))
        (fun i _ _ => mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (ha i))
  calc B0 * (∑ i ∈ Finset.range (m + 1), (i.factorial : ℝ)⁻¹ * a i) +
        B1 * (∑ i ∈ Finset.range (m + 1),
          (i.factorial : ℝ)⁻¹ * (i : ℝ) * (if 1 ≤ i then a (i - 1) else 0))
      ≤ B0 * (∑ i ∈ Finset.range (m + 1), (i.factorial : ℝ)⁻¹ * a i) +
        B1 * (∑ i ∈ Finset.range (m + 1), (i.factorial : ℝ)⁻¹ * a i) := by gcongr
    _ = (B0 + B1) * (∑ i ∈ Finset.range (m + 1), (i.factorial : ℝ)⁻¹ * a i) := by ring

lemma fderiv_clm_eq_const {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (L : E →L[ℝ] G) :
    fderiv ℝ L = fun _ => L := by
  funext x
  exact ContinuousLinearMap.fderiv L

lemma iteratedFDeriv_const_succ {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (c : G) (m : ℕ) (x : E) :
    iteratedFDeriv ℝ (m + 1) (fun _ => c) x = 0 := by
  rw [iteratedFDeriv_succ_const m c]
  rfl

lemma norm_iteratedFDeriv_clm_succ_succ {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (L : E →L[ℝ] G) (x : E) (m : ℕ) :
    ‖iteratedFDeriv ℝ (m + 2) L x‖ = 0 := by
  have h_norm : ‖iteratedFDeriv ℝ (m + 2) L x‖ = ‖iteratedFDeriv ℝ (m + 1) (fderiv ℝ L) x‖ := by
    rw [show m + 2 = (m + 1) + 1 from rfl]
    exact norm_iteratedFDeriv_fderiv.symm
  rw [fderiv_clm_eq_const, iteratedFDeriv_const_succ, norm_zero] at h_norm
  exact h_norm

lemma iteratedFDeriv_clm_ge_two {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (L : E →L[ℝ] G) (x : E) (i : ℕ) (hi : 2 ≤ i) :
    iteratedFDeriv ℝ i L x = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hi
  have h : ‖iteratedFDeriv ℝ (m + 2) L x‖ = 0 := norm_iteratedFDeriv_clm_succ_succ L x m
  have h_eq : 2 + m = m + 2 := add_comm 2 m
  rw [h_eq]
  exact norm_eq_zero.mp h

lemma norm_iteratedFDeriv_clm_mul_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] ℂ) (g : E → ℂ) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (p : E) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (fun y => L y * g y) p‖ ≤
      ‖L p‖ * ‖iteratedFDeriv ℝ m g p‖ +
        (m : ℝ) * ‖L‖ * (if 1 ≤ m then ‖iteratedFDeriv ℝ (m - 1) g p‖ else 0) := by
  cases m with
  | zero =>
    simp only [norm_iteratedFDeriv_zero, Nat.cast_zero, zero_mul, add_zero]
    exact norm_mul_le (L p) (g p)
  | succ m' =>
    rw [if_pos (by omega)]
    have h_sub : m' + 1 - 1 = m' := rfl
    rw [h_sub]
    have h_le := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (f := ⇑L) (g := g)
      (n := m' + 1) (N := (⊤ : ℕ∞))
      L.contDiff hg p (WithTop.coe_le_coe.mpr le_top)
    refine h_le.trans ?_
    rw [Finset.sum_range_succ']
    have h0 : ((m' + 1).choose 0 : ℝ) * ‖iteratedFDeriv ℝ 0 L p‖ *
          ‖iteratedFDeriv ℝ (m' + 1 - 0) g p‖ =
        ‖L p‖ * ‖iteratedFDeriv ℝ (m' + 1) g p‖ := by
      rw [Nat.sub_zero]
      simp only [Nat.choose_zero_right, Nat.cast_one, norm_iteratedFDeriv_zero, one_mul]
    rw [h0]
    rw [Finset.sum_range_succ']
    have h1 : ((m' + 1).choose 1 : ℝ) * ‖iteratedFDeriv ℝ 1 L p‖ *
          ‖iteratedFDeriv ℝ (m' + 1 - 1) g p‖ =
        ((m' + 1 : ℕ) : ℝ) * ‖L‖ * ‖iteratedFDeriv ℝ m' g p‖ := by
      rw [Nat.choose_one_right, norm_iteratedFDeriv_one]
      have : fderiv ℝ L p = L := ContinuousLinearMap.fderiv L
      rw [this]
      have h_sub' : m' + 1 - 1 = m' := rfl
      rw [h_sub']
    rw [h1]
    have h_tail : ∀ i ∈ Finset.range m',
        ((m' + 1).choose (i + 1 + 1) : ℝ) * ‖iteratedFDeriv ℝ (i + 1 + 1) L p‖ *
          ‖iteratedFDeriv ℝ (m' + 1 - (i + 1 + 1)) g p‖ = 0 := by
      intro i _
      have hi2 : 2 ≤ i + 1 + 1 := by omega
      have hz := iteratedFDeriv_clm_ge_two L p (i + 1 + 1) hi2
      rw [hz, norm_zero, mul_zero, zero_mul]
    have h_sum_zero : (∑ i ∈ Finset.range m', ((m' + 1).choose (i + 1 + 1) : ℝ) *
        ‖iteratedFDeriv ℝ (i + 1 + 1) L p‖ * ‖iteratedFDeriv ℝ (m' + 1 - (i + 1 + 1)) g p‖) = 0 :=
      Finset.sum_eq_zero h_tail
    rw [h_sum_zero, zero_add, add_comm]

noncomputable def vladimirov_taylor_norm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (m : ℕ) (f : E → ℂ) (p : E) : ℝ :=
  ∑ i ∈ Finset.range (m + 1), (i.factorial : ℝ)⁻¹ * ‖iteratedFDeriv ℝ i f p‖

lemma vladimirov_taylor_norm_nonneg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (m : ℕ) (f : E → ℂ) (p : E) :
    0 ≤ vladimirov_taylor_norm m f p := by
  refine Finset.sum_nonneg (fun i _ =>
    mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (norm_nonneg _))

lemma norm_iteratedFDeriv_le_factorial_mul_taylor_norm {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (m : ℕ) (f : E → ℂ) (p : E) :
    ‖iteratedFDeriv ℝ m f p‖ ≤ (m.factorial : ℝ) * vladimirov_taylor_norm m f p := by
  have h_in : m ∈ Finset.range (m + 1) := Finset.self_mem_range_succ m
  have h_term : (m.factorial : ℝ)⁻¹ * ‖iteratedFDeriv ℝ m f p‖ ≤ vladimirov_taylor_norm m f p := by
    dsimp [vladimirov_taylor_norm]
    exact Finset.single_le_sum (f := fun i => (i.factorial : ℝ)⁻¹ * ‖iteratedFDeriv ℝ i f p‖)
      (fun i _ => mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (norm_nonneg _)) h_in
  have h_pos : 0 < (m.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos m)
  calc ‖iteratedFDeriv ℝ m f p‖
      = (m.factorial : ℝ) * ((m.factorial : ℝ)⁻¹ * ‖iteratedFDeriv ℝ m f p‖) := by
        rw [← mul_assoc, mul_inv_cancel₀ h_pos.ne', one_mul]
    _ ≤ (m.factorial : ℝ) * vladimirov_taylor_norm m f p :=
        mul_le_mul_of_nonneg_left h_term (by positivity)

lemma vladimirov_taylor_norm_clm_mul_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (m : ℕ) (L : E →L[ℝ] ℂ) (g : E → ℂ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (p : E) (B0 B1 : ℝ) (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1)
    (hLp : ‖L p‖ ≤ B0) (hL : ‖L‖ ≤ B1) :
    vladimirov_taylor_norm m (fun y => L y * g y) p ≤
      (B0 + B1) * vladimirov_taylor_norm m g p := by
  have h_term : ∀ i ∈ Finset.range (m + 1),
      (i.factorial : ℝ)⁻¹ * ‖iteratedFDeriv ℝ i (fun y => L y * g y) p‖ ≤
      (i.factorial : ℝ)⁻¹ * (B0 * ‖iteratedFDeriv ℝ i g p‖ +
        (i : ℝ) * B1 * (if 1 ≤ i then ‖iteratedFDeriv ℝ (i - 1) g p‖ else 0)) := by
    intro i _
    have h_le := norm_iteratedFDeriv_clm_mul_le L g hg p i
    have h_B0 : ‖L p‖ * ‖iteratedFDeriv ℝ i g p‖ ≤ B0 * ‖iteratedFDeriv ℝ i g p‖ := by gcongr
    have h_B1 : (i : ℝ) * ‖L‖ * (if 1 ≤ i then ‖iteratedFDeriv ℝ (i - 1) g p‖ else 0) ≤
        (i : ℝ) * B1 * (if 1 ≤ i then ‖iteratedFDeriv ℝ (i - 1) g p‖ else 0) := by gcongr
    have h_add := add_le_add h_B0 h_B1
    exact mul_le_mul_of_nonneg_left (h_le.trans h_add) (inv_nonneg.mpr (Nat.cast_nonneg _))
  have h_sum := Finset.sum_le_sum h_term
  have h_bound := taylor_sum_bound m (fun i => ‖iteratedFDeriv ℝ i g p‖)
    (fun i => norm_nonneg _) B0 B1 hB0 hB1
  exact h_sum.trans h_bound

lemma vladimirov_multilinear_psi_taylor_norm_le (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z : Fin (n + 1) → Fin 4 → ℂ) (m : ℕ) (B B_op : ℝ) (hB_nonneg : 0 ≤ B) (hB_op_nonneg : 0 ≤ B_op)
    (hB : ∀ (i : Fin (n + 1) × Fin 4) p,
      p ∈ Function.support (vladimirovCutoffBump (n + 1) R hR) →
      ‖vladimirov_phase_CLM (n + 1) (vladimirov_basis (n + 1) i) p‖ ≤ B)
    (hB_op : ∀ i : Fin (n + 1) × Fin 4,
      ‖vladimirov_phase_CLM (n + 1) (vladimirov_basis (n + 1) i)‖ ≤ B_op)
    (k : ℕ) (j : Fin k → Fin (n + 1) × Fin 4)
    (p : Fin (n + 1) → Fin 4 → ℝ) (hp : p ∈ Function.support (vladimirovCutoffBump (n + 1) R hR)) :
    vladimirov_taylor_norm m
      (vladimirov_multilinear_psi (n + 1) R hR z k (fun m => vladimirov_basis (n + 1) (j m))) p ≤
      (B + B_op) ^ k * vladimirov_taylor_norm m (vladimirov_psi (n + 1) R hR z) p := by
  induction k with
  | zero =>
    simp only [pow_zero, one_mul]
    have h_zero :
        vladimirov_multilinear_psi (n + 1) R hR z 0 (fun m => vladimirov_basis (n + 1) (j m)) =
        vladimirov_psi (n + 1) R hR z := by
      ext y
      exact vladimirov_multilinear_psi_zero (n + 1) R hR z
        (fun m => vladimirov_basis (n + 1) (j m)) y
    rw [h_zero]
  | succ k' ih =>
    rw [pow_succ]
    have h_succ := vladimirov_multilinear_psi_succ (n + 1) R hR z k'
      (fun m => vladimirov_basis (n + 1) (j m))
    have h_fun :
        (vladimirov_multilinear_psi (n + 1) R hR z (k' + 1)
          (fun m => vladimirov_basis (n + 1) (j m))) =
        fun y => (vladimirov_phase_CLM (n + 1) (vladimirov_basis (n + 1) (j 0)) y) *
          (vladimirov_multilinear_psi (n + 1) R hR z k'
            (fun m => vladimirov_basis (n + 1) (j (Fin.succ m))) y) := by
      ext y
      exact h_succ y
    rw [h_fun]
    have hg_diff : ContDiff ℝ (⊤ : ℕ∞)
      (vladimirov_multilinear_psi (n + 1) R hR z k'
        (fun m => vladimirov_basis (n + 1) (j (Fin.succ m)))) :=
      vladimirov_multilinear_psi_contDiff (n + 1) R hR z k'
        (fun m => vladimirov_basis (n + 1) (j (Fin.succ m)))
    have h_step := vladimirov_taylor_norm_clm_mul_le m
      (vladimirov_phase_CLM (n + 1) (vladimirov_basis (n + 1) (j 0)))
      (vladimirov_multilinear_psi (n + 1) R hR z k'
        (fun m => vladimirov_basis (n + 1) (j (Fin.succ m))))
      hg_diff p B B_op hB_nonneg hB_op_nonneg (hB (j 0) p hp) (hB_op (j 0))
    have h_rec := ih (fun m => j (Fin.succ m))
    calc vladimirov_taylor_norm m
          (fun y => (vladimirov_phase_CLM (n + 1) (vladimirov_basis (n + 1) (j 0)) y) *
            (vladimirov_multilinear_psi (n + 1) R hR z k'
              (fun m => vladimirov_basis (n + 1) (j (Fin.succ m))) y)) p
        ≤ (B + B_op) * vladimirov_taylor_norm m
            (vladimirov_multilinear_psi (n + 1) R hR z k'
              (fun m => vladimirov_basis (n + 1) (j (Fin.succ m)))) p := h_step
      _ ≤ (B + B_op) *
          ((B + B_op) ^ k' * vladimirov_taylor_norm m (vladimirov_psi (n + 1) R hR z) p) := by
        exact mul_le_mul_of_nonneg_left h_rec (by positivity)
      _ = (B + B_op) ^ (k' + 1) *
          vladimirov_taylor_norm m (vladimirov_psi (n + 1) R hR z) p := by ring

lemma vladimirov_multilinear_psi_taylor_norm_ball_le (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z : Fin (n + 1) → Fin 4 → ℂ) (m : ℕ) (B_op : ℝ) (hB_op_nonneg : 0 ≤ B_op)
    (hB_op : ∀ i : Fin (n + 1) × Fin 4,
      ‖vladimirov_phase_CLM (n + 1) (vladimirov_basis (n + 1) i)‖ ≤ B_op)
    (k : ℕ) (j : Fin k → Fin (n + 1) × Fin 4)
    (p : Fin (n + 1) → Fin 4 → ℝ) (hp : ‖p‖ ≤ 2 * R) :
    vladimirov_taylor_norm m
      (vladimirov_multilinear_psi (n + 1) R hR z k (fun m => vladimirov_basis (n + 1) (j m))) p ≤
      (B_op * (2 * R) + B_op) ^ k * vladimirov_taylor_norm m (vladimirov_psi (n + 1) R hR z) p := by
  induction k with
  | zero =>
    simp only [pow_zero, one_mul]
    have h_zero :
        vladimirov_multilinear_psi (n + 1) R hR z 0 (fun m => vladimirov_basis (n + 1) (j m)) =
        vladimirov_psi (n + 1) R hR z := by
      ext y
      exact vladimirov_multilinear_psi_zero (n + 1) R hR z
        (fun m => vladimirov_basis (n + 1) (j m)) y
    rw [h_zero]
  | succ k' ih =>
    rw [pow_succ]
    have h_succ := vladimirov_multilinear_psi_succ (n + 1) R hR z k'
      (fun m => vladimirov_basis (n + 1) (j m))
    have h_fun :
        (vladimirov_multilinear_psi (n + 1) R hR z (k' + 1)
          (fun m => vladimirov_basis (n + 1) (j m))) =
        fun y => (vladimirov_phase_CLM (n + 1) (vladimirov_basis (n + 1) (j 0)) y) *
          (vladimirov_multilinear_psi (n + 1) R hR z k'
            (fun m => vladimirov_basis (n + 1) (j (Fin.succ m))) y) := by
      ext y
      exact h_succ y
    rw [h_fun]
    have hg_diff : ContDiff ℝ (⊤ : ℕ∞)
      (vladimirov_multilinear_psi (n + 1) R hR z k'
        (fun m => vladimirov_basis (n + 1) (j (Fin.succ m)))) :=
      vladimirov_multilinear_psi_contDiff (n + 1) R hR z k'
        (fun m => vladimirov_basis (n + 1) (j (Fin.succ m)))
    have h_Lp : ‖vladimirov_phase_CLM (n + 1) (vladimirov_basis (n + 1) (j 0)) p‖ ≤
        B_op * (2 * R) := by
      have h1 := (vladimirov_phase_CLM (n + 1) (vladimirov_basis (n + 1) (j 0))).le_opNorm p
      have h2 := hB_op (j 0)
      have hR_nonneg : 0 ≤ 2 * R := by linarith
      calc ‖vladimirov_phase_CLM (n + 1) (vladimirov_basis (n + 1) (j 0)) p‖
          ≤ ‖vladimirov_phase_CLM (n + 1) (vladimirov_basis (n + 1) (j 0))‖ * ‖p‖ := h1
        _ ≤ B_op * (2 * R) := by gcongr
    have hB0_nonneg : 0 ≤ B_op * (2 * R) := mul_nonneg hB_op_nonneg (by linarith)
    have h_step := vladimirov_taylor_norm_clm_mul_le m
      (vladimirov_phase_CLM (n + 1) (vladimirov_basis (n + 1) (j 0)))
      (vladimirov_multilinear_psi (n + 1) R hR z k'
        (fun m => vladimirov_basis (n + 1) (j (Fin.succ m))))
      hg_diff p (B_op * (2 * R)) B_op hB0_nonneg hB_op_nonneg h_Lp (hB_op (j 0))
    have h_rec := ih (fun m => j (Fin.succ m))
    calc vladimirov_taylor_norm m
          (fun y => (vladimirov_phase_CLM (n + 1) (vladimirov_basis (n + 1) (j 0)) y) *
            (vladimirov_multilinear_psi (n + 1) R hR z k'
              (fun m => vladimirov_basis (n + 1) (j (Fin.succ m))) y)) p
        ≤ (B_op * (2 * R) + B_op) * vladimirov_taylor_norm m
            (vladimirov_multilinear_psi (n + 1) R hR z k'
              (fun m => vladimirov_basis (n + 1) (j (Fin.succ m)))) p := h_step
      _ ≤ (B_op * (2 * R) + B_op) *
          ((B_op * (2 * R) + B_op) ^ k' *
            vladimirov_taylor_norm m (vladimirov_psi (n + 1) R hR z) p) := by
        exact mul_le_mul_of_nonneg_left h_rec (by positivity)
      _ = (B_op * (2 * R) + B_op) ^ (k' + 1) *
          vladimirov_taylor_norm m (vladimirov_psi (n + 1) R hR z) p := by ring

lemma vladimirov_multilinear_psi_schwartz_finset_bound (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z : Fin (n + 1) → Fin 4 → ℂ) (s : Finset (ℕ × ℕ))
    (h_single : ∀ lm ∈ s, ∃ C M : ℝ, 0 ≤ C ∧ 0 ≤ M ∧
      ∀ (k : ℕ) (j : Fin k → Fin (n + 1) × Fin 4),
        (schwartzSeminormFamily ℝ (Fin (n + 1) → Fin 4 → ℝ) ℂ lm)
          (vladimirov_multilinear_psi_schwartz (n + 1) R hR z k
            (fun m => vladimirov_basis (n + 1) (j m))) ≤ C * M ^ k) :
    ∃ C M : ℝ, 0 ≤ C ∧ 0 ≤ M ∧ ∀ (k : ℕ) (j : Fin k → Fin (n + 1) × Fin 4),
      (s.sup (schwartzSeminormFamily ℝ (Fin (n + 1) → Fin 4 → ℝ) ℂ))
        (vladimirov_multilinear_psi_schwartz (n + 1) R hR z k
          (fun m => vladimirov_basis (n + 1) (j m))) ≤ C * M ^ k := by
  induction s using Finset.induction_on with
  | empty =>
    use 0, 0
    refine ⟨le_rfl, le_rfl, ?_⟩
    intro k j
    rw [Finset.sup_empty, Seminorm.bot_eq_zero]
    simp only [_root_.zero_apply, zero_mul, le_refl]
  | @insert a s' ha ih =>
    have h_single_a := h_single a (Finset.mem_insert_self a s')
    have h_single_s : ∀ lm ∈ s', _ := fun lm hlm => h_single lm (Finset.mem_insert_of_mem hlm)
    obtain ⟨Ca, Ma, hCa_nonneg, hMa_nonneg, h_a⟩ := h_single_a
    obtain ⟨Cs, Ms, hCs_nonneg, hMs_nonneg, h_s⟩ := ih h_single_s
    let C := max Ca Cs
    let M := max Ma Ms
    have hC_nonneg : 0 ≤ C := le_max_of_le_left hCa_nonneg
    have hM_nonneg : 0 ≤ M := le_max_of_le_left hMa_nonneg
    use C, M
    refine ⟨hC_nonneg, hM_nonneg, ?_⟩
    intro k j
    rw [Finset.sup_insert, Seminorm.sup_apply]
    have ha_le : Ca * Ma ^ k ≤ C * M ^ k := by
      gcongr
      · exact le_max_left Ca Cs
      · exact le_max_left Ma Ms
    have hs_le : Cs * Ms ^ k ≤ C * M ^ k := by
      gcongr
      · exact le_max_right Ca Cs
      · exact le_max_right Ma Ms
    exact max_le ((h_a k j).trans ha_le) ((h_s k j).trans hs_le)

lemma vladimirov_multilinear_psi_support_subset (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z : Fin n → Fin 4 → ℂ) (k : ℕ) (h : Fin k → (Fin n → Fin 4 → ℂ)) :
    Function.support (vladimirov_multilinear_psi n R hR z k h) ⊆
      Function.support (vladimirovCutoffBump n R hR) := by
  intro p hp
  rw [Function.mem_support] at hp ⊢
  intro h_bump
  apply hp
  dsimp [vladimirov_multilinear_psi, vladimirov_psi]
  rw [h_bump, Complex.ofReal_zero, zero_mul, mul_zero]

lemma vladimirov_multilinear_psi_tsupport_subset (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z : Fin n → Fin 4 → ℂ) (k : ℕ) (h : Fin k → (Fin n → Fin 4 → ℂ)) :
    tsupport (vladimirov_multilinear_psi n R hR z k h) ⊆ Metric.closedBall 0 (2 * R) := by
  have h_sub := vladimirov_multilinear_psi_support_subset n R hR z k h
  have h_clos := closure_mono h_sub
  have h_tsupp : tsupport (vladimirovCutoffBump n R hR) = Metric.closedBall 0 (2 * R) :=
    (vladimirovCutoffBump n R hR).tsupport_eq
  exact h_clos.trans (le_of_eq h_tsupp)

lemma vladimirov_multilinear_psi_iteratedFDeriv_eq_zero (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z : Fin n → Fin 4 → ℂ) (k : ℕ) (h : Fin k → (Fin n → Fin 4 → ℂ)) (m : ℕ)
    (p : Fin n → Fin 4 → ℝ) (hp : 2 * R < ‖p‖) :
    iteratedFDeriv ℝ m (vladimirov_multilinear_psi n R hR z k h) p = 0 := by
  have h_supp : Function.support (iteratedFDeriv ℝ m (vladimirov_multilinear_psi n R hR z k h)) ⊆
      Metric.closedBall 0 (2 * R) :=
    (support_iteratedFDeriv_subset m).trans
      (vladimirov_multilinear_psi_tsupport_subset n R hR z k h)
  by_contra h_ne
  have h_in : p ∈ Function.support (iteratedFDeriv ℝ m (vladimirov_multilinear_psi n R hR z k h)) :=
    Function.mem_support.mpr h_ne
  have h_ball : p ∈ Metric.closedBall (0 : Fin n → Fin 4 → ℝ) (2 * R) := h_supp h_in
  rw [Metric.mem_closedBall, dist_zero_right] at h_ball
  linarith

lemma vladimirov_taylor_norm_psi_le (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z : Fin (n + 1) → Fin 4 → ℂ) (m : ℕ) (p : Fin (n + 1) → Fin 4 → ℝ) :
    vladimirov_taylor_norm m (vladimirov_psi (n + 1) R hR z) p ≤
      ∑ i ∈ Finset.range (m + 1), (i.factorial : ℝ)⁻¹ *
        (schwartzSeminormFamily ℝ (Fin (n + 1) → Fin 4 → ℝ) ℂ (0, i))
          (vladimirov_psi_schwartz (n + 1) R hR z) := by
  dsimp [vladimirov_taylor_norm]
  refine Finset.sum_le_sum (fun i _ => ?_)
  have h_le := (vladimirov_psi_schwartz (n + 1) R hR z).le_seminorm (𝕜 := ℝ) 0 i p
  rw [pow_zero, one_mul] at h_le
  exact mul_le_mul_of_nonneg_left h_le (inv_nonneg.mpr (Nat.cast_nonneg _))

lemma vladimirov_multilinear_psi_schwartz_seminorm_bound (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z : Fin (n + 1) → Fin 4 → ℂ) (l m : ℕ) :
    ∃ C M : ℝ, 0 ≤ C ∧ 0 ≤ M ∧ ∀ (k : ℕ) (j : Fin k → Fin (n + 1) × Fin 4),
      (schwartzSeminormFamily ℝ (Fin (n + 1) → Fin 4 → ℝ) ℂ (l, m))
        (vladimirov_multilinear_psi_schwartz (n + 1) R hR z k
          (fun m => vladimirov_basis (n + 1) (j m))) ≤ C * M ^ k := by
  let B_op : ℝ := ∑ i : Fin (n + 1) × Fin 4,
    ‖vladimirov_phase_CLM (n + 1) (vladimirov_basis (n + 1) i)‖
  have hB_op_nonneg : 0 ≤ B_op := by
    dsimp [B_op]
    exact Finset.sum_nonneg (fun (x : Fin (n + 1) × Fin 4) _ =>
      norm_nonneg (vladimirov_phase_CLM (n + 1) (vladimirov_basis (n + 1) x)))
  have hB_op : ∀ i, ‖vladimirov_phase_CLM (n + 1) (vladimirov_basis (n + 1) i)‖ ≤ B_op := by
    intro i
    dsimp [B_op]
    exact Finset.single_le_sum (fun (x : Fin (n + 1) × Fin 4) _ =>
      norm_nonneg (vladimirov_phase_CLM (n + 1) (vladimirov_basis (n + 1) x))) (Finset.mem_univ i)
  let M := B_op * (2 * R) + B_op
  have hM_nonneg : 0 ≤ M := add_nonneg (mul_nonneg hB_op_nonneg (by linarith)) hB_op_nonneg
  let C_psi := ∑ i ∈ Finset.range (m + 1), (i.factorial : ℝ)⁻¹ *
    (schwartzSeminormFamily ℝ (Fin (n + 1) → Fin 4 → ℝ) ℂ (0, i))
      (vladimirov_psi_schwartz (n + 1) R hR z)
  have hC_psi_nonneg : 0 ≤ C_psi := by
    dsimp [C_psi]
    exact Finset.sum_nonneg (fun i _ =>
      mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (apply_nonneg _ _))
  let C := (2 * R) ^ l * (m.factorial : ℝ) * C_psi
  have hC_nonneg : 0 ≤ C :=
    mul_nonneg (mul_nonneg (by positivity) (Nat.cast_nonneg _)) hC_psi_nonneg
  use C, M
  refine ⟨hC_nonneg, hM_nonneg, ?_⟩
  intro k j
  change (SchwartzMap.seminorm ℝ l m)
    (vladimirov_multilinear_psi_schwartz (n + 1) R hR z k
      (fun m => vladimirov_basis (n + 1) (j m))) ≤ C * M ^ k
  refine SchwartzMap.seminorm_le_bound ℝ l m _ (by positivity) ?_
  intro p
  have h_fun_eq :
      ⇑(vladimirov_multilinear_psi_schwartz (n + 1) R hR z k
        (fun m => vladimirov_basis (n + 1) (j m))) =
      vladimirov_multilinear_psi (n + 1) R hR z k
        (fun m => vladimirov_basis (n + 1) (j m)) := rfl
  rw [h_fun_eq]
  by_cases hp : ‖p‖ ≤ 2 * R
  · have h_pl : ‖p‖ ^ l ≤ (2 * R) ^ l := by gcongr
    have h_deriv := norm_iteratedFDeriv_le_factorial_mul_taylor_norm m
      (vladimirov_multilinear_psi (n + 1) R hR z k (fun m => vladimirov_basis (n + 1) (j m))) p
    have h_taylor := vladimirov_multilinear_psi_taylor_norm_ball_le n R hR z m
      B_op hB_op_nonneg hB_op k j p hp
    have h_psi := vladimirov_taylor_norm_psi_le n R hR z m p
    calc ‖p‖ ^ l *
          ‖iteratedFDeriv ℝ m (vladimirov_multilinear_psi (n + 1) R hR z k
            (fun m => vladimirov_basis (n + 1) (j m))) p‖
        ≤ (2 * R) ^ l * ((m.factorial : ℝ) *
            vladimirov_taylor_norm m (vladimirov_multilinear_psi (n + 1) R hR z k
              (fun m => vladimirov_basis (n + 1) (j m))) p) := by gcongr
      _ ≤ (2 * R) ^ l * ((m.factorial : ℝ) *
            (M ^ k * vladimirov_taylor_norm m (vladimirov_psi (n + 1) R hR z) p)) := by gcongr
      _ ≤ (2 * R) ^ l * ((m.factorial : ℝ) * (M ^ k * C_psi)) := by gcongr
      _ = C * M ^ k := by ring
  · have hp_lt : 2 * R < ‖p‖ := not_le.mp hp
    have h_zero := vladimirov_multilinear_psi_iteratedFDeriv_eq_zero (n + 1) R hR z k
      (fun m => vladimirov_basis (n + 1) (j m)) m p hp_lt
    rw [h_zero, norm_zero, mul_zero]
    positivity

lemma vladimirov_multilinear_psi_schwartz_T_bound (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z : Fin n → Fin 4 → ℂ) (T : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ →L[ℂ] ℂ) :
    ∃ C M : ℝ, 0 ≤ C ∧ 0 ≤ M ∧ ∀ (k : ℕ) (j : Fin k → Fin n × Fin 4),
      ‖T (vladimirov_multilinear_psi_schwartz n R hR z k
        (fun m => vladimirov_basis n (j m)))‖ ≤ C * M ^ k := by
  cases n with
  | zero =>
    let j0 : Fin 0 → Fin 0 × Fin 4 := Fin.elim0
    use ‖T (vladimirov_multilinear_psi_schwartz 0 R hR z 0 (fun m => vladimirov_basis 0 (j0 m)))‖, 0
    refine ⟨norm_nonneg _, le_rfl, ?_⟩
    intro k j
    cases k with
    | zero =>
      simp only [pow_zero, mul_one]
      have : j = j0 := Subsingleton.elim _ _
      subst this
      exact le_rfl
    | succ k' =>
      exact False.elim (Fin.elim0 (j 0).1)
  | succ n =>
    obtain ⟨s, CT, hCT_pos, hT_bound⟩ := schwartz_clm_bound (n + 1) T
    have h_single_bound : ∀ lm ∈ s, ∃ C M : ℝ, 0 ≤ C ∧ 0 ≤ M ∧
        ∀ (k : ℕ) (j : Fin k → Fin (n + 1) × Fin 4),
          (schwartzSeminormFamily ℝ (Fin (n + 1) → Fin 4 → ℝ) ℂ lm)
            (vladimirov_multilinear_psi_schwartz (n + 1) R hR z k
              (fun m => vladimirov_basis (n + 1) (j m))) ≤ C * M ^ k := by
      intro lm _
      exact vladimirov_multilinear_psi_schwartz_seminorm_bound n R hR z lm.1 lm.2
    obtain ⟨Cs, M, hCs_nonneg, hM_nonneg, h_sup_le⟩ :=
      vladimirov_multilinear_psi_schwartz_finset_bound n R hR z s h_single_bound
    use CT * Cs, M
    refine ⟨by positivity, hM_nonneg, ?_⟩
    intro k j
    have hT := hT_bound
      (vladimirov_multilinear_psi_schwartz (n + 1) R hR z k
        (fun m => vladimirov_basis (n + 1) (j m)))
    have h_sup := h_sup_le k j
    calc ‖T (vladimirov_multilinear_psi_schwartz (n + 1) R hR z k
          (fun m => vladimirov_basis (n + 1) (j m)))‖
        ≤ CT * (s.sup (schwartzSeminormFamily ℝ (Fin (n + 1) → Fin 4 → ℝ) ℂ))
            (vladimirov_multilinear_psi_schwartz (n + 1) R hR z k
              (fun m => vladimirov_basis (n + 1) (j m))) := hT
      _ ≤ CT * (Cs * M ^ k) := mul_le_mul_of_nonneg_left h_sup hCT_pos.le
      _ = (CT * Cs) * M ^ k := by ring

lemma vladimirov_formal_series_radius_pos (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z : Fin n → Fin 4 → ℂ) (T : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ →L[ℂ] ℂ) :
    0 < (vladimirov_formal_series n R hR z T).radius := by
  let p := vladimirov_formal_series n R hR z T
  obtain ⟨C_bound, M, hC_nonneg, hM_nonneg, hM⟩ :=
    vladimirov_multilinear_psi_schwartz_T_bound n R hR z T
  let A : ℝ := (Fintype.card (Fin n × Fin 4) : ℝ) * M
  have h_bound : ∃ C : ℝ, ∀ k : ℕ, ‖p k‖ * (1 : ℝ) ^ k ≤ C := by
    use C_bound * Real.exp (max A 0)
    intro k
    rw [one_pow, mul_one]
    have h_le := vladimirov_taylor_multilinear_norm_le n R hR z T k
    refine h_le.trans ?_
    have h_term : ∀ j : Fin k → Fin n × Fin 4,
        ‖vladimirov_basis_coeff n R hR z T k j‖ ≤ C_bound * ((k.factorial : ℝ)⁻¹ * M ^ k) := by
      intro j
      rw [vladimirov_basis_coeff_norm]
      have hMj := hM k j
      calc (k.factorial : ℝ)⁻¹ *
            ‖T (vladimirov_multilinear_psi_schwartz n R hR z k
              (fun m => vladimirov_basis n (j m)))‖
          ≤ (k.factorial : ℝ)⁻¹ * (C_bound * M ^ k) :=
            mul_le_mul_of_nonneg_left hMj (by positivity)
        _ = C_bound * ((k.factorial : ℝ)⁻¹ * M ^ k) := by ring
    have h_sum_le : (∑ j : Fin k → Fin n × Fin 4, ‖vladimirov_basis_coeff n R hR z T k j‖) ≤
        ∑ j : Fin k → Fin n × Fin 4, C_bound * ((k.factorial : ℝ)⁻¹ * M ^ k) :=
      Finset.sum_le_sum fun j _ => h_term j
    refine h_sum_le.trans ?_
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [Fintype.card_fun, Fintype.card_fin]
    have h_card :
        ((Fintype.card (Fin n × Fin 4) ^ k : ℕ) : ℝ) = (Fintype.card (Fin n × Fin 4) : ℝ) ^ k := by
      push_cast; rfl
    rw [h_card]
    have h_reorder :
        (Fintype.card (Fin n × Fin 4) : ℝ) ^ k * (C_bound * ((k.factorial : ℝ)⁻¹ * M ^ k)) =
        C_bound * (((Fintype.card (Fin n × Fin 4) : ℝ) * M) ^ k / (k.factorial : ℝ)) := by
      rw [mul_pow]
      ring
    rw [h_reorder]
    change C_bound * (A ^ k / (k.factorial : ℝ)) ≤ C_bound * Real.exp (max A 0)
    have hA_le : A ^ k / (k.factorial : ℝ) ≤ (max A 0) ^ k / (k.factorial : ℝ) := by
      gcongr
      exact le_max_left A 0
    have h_nonneg : 0 ≤ max A 0 := le_max_right A 0
    have h_in : k ∈ Finset.range (k + 1) := Finset.self_mem_range_succ k
    have h_term_le_sum : max A 0 ^ k / (k.factorial : ℝ) ≤
        ∑ i ∈ Finset.range (k + 1), max A 0 ^ i / (i.factorial : ℝ) := by
      refine Finset.single_le_sum (f := fun i => max A 0 ^ i / (i.factorial : ℝ)) ?_ h_in
      intro i _
      exact div_nonneg (pow_nonneg h_nonneg i) (Nat.cast_nonneg _)
    have h_exp := Real.sum_le_exp_of_nonneg h_nonneg (k + 1)
    have h_tot : A ^ k / (k.factorial : ℝ) ≤ Real.exp (max A 0) :=
      hA_le.trans (h_term_le_sum.trans h_exp)
    exact mul_le_mul_of_nonneg_left h_tot hC_nonneg
  obtain ⟨C, hC⟩ := h_bound
  have h_le : (1 : ENNReal) ≤ p.radius := by
    have h_le' := FormalMultilinearSeries.le_radius_of_bound (p := p) C (r := (1 : NNReal)) (by
      intro k
      simpa using hC k)
    exact h_le'
  exact lt_of_lt_of_le one_pos h_le

lemma vladimirov_slice_differentiable (n : ℕ) (hn : ¬ n ≤ 1) (R : ℝ) (hR : 0 < R)
    (z y : Fin n → Fin 4 → ℂ) (T : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ →L[ℂ] ℂ) :
    Differentiable ℂ (fun t : ℂ => T (vladimirov_psi_schwartz n R hR (z + t • y))) := by
  apply slice_differentiable_schwartz_family n R hR z y T
  intro w
  exact differentiable_schwartz_family_ge_two n hn R hR w T

lemma vladimirov_slice_hasFPowerSeriesOnBall (n : ℕ) (hn : ¬ n ≤ 1) (R : ℝ) (hR : 0 < R)
    (z y : Fin n → Fin 4 → ℂ) (T : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ →L[ℂ] ℂ) :
    HasFPowerSeriesOnBall (fun t : ℂ => T (vladimirov_psi_schwartz n R hR (z + t • y)))
      (cauchyPowerSeries (fun t : ℂ => T (vladimirov_psi_schwartz n R hR (z + t • y)))
        (0 : ℂ) (1 : ℝ))
      0 ⊤ := by
  have hd := vladimirov_slice_differentiable n hn R hR z y T
  exact hd.hasFPowerSeriesOnBall (0 : ℂ) (R := (1 : NNReal)) zero_lt_one

lemma vladimirov_slice_eval_eq_sum (n : ℕ) (hn : ¬ n ≤ 1) (R : ℝ) (hR : 0 < R)
    (z y : Fin n → Fin 4 → ℂ) (T : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ →L[ℂ] ℂ) :
    T (vladimirov_psi_schwartz n R hR (z + y)) =
      (cauchyPowerSeries (fun t : ℂ => T (vladimirov_psi_schwartz n R hR (z + t • y)))
        (0 : ℂ) (1 : ℝ)).sum 1 := by
  have hP := vladimirov_slice_hasFPowerSeriesOnBall n hn R hR z y T
  have h1 : (1 : ℂ) ∈ Metric.eball (0 : ℂ) ⊤ := by
    rw [Metric.eball_top]
    trivial
  have h_sum := hP.sum h1
  change (fun t : ℂ => T (vladimirov_psi_schwartz n R hR (z + t • y))) (0 + 1) = _ at h_sum
  rw [zero_add] at h_sum
  dsimp only at h_sum
  rw [one_smul] at h_sum
  exact h_sum

lemma cauchyPowerSeries_one_eq_iteratedDeriv
    (g : ℂ → ℂ) (hg : Differentiable ℂ g) (k : ℕ) :
    (cauchyPowerSeries g 0 1 k (fun _ => 1)) =
      ((k.factorial : ℝ) : ℂ)⁻¹ * iteratedDeriv k g 0 := by
  have hP : HasFPowerSeriesOnBall g (cauchyPowerSeries g 0 1) 0 ⊤ :=
    hg.hasFPowerSeriesOnBall 0 (R := (1 : NNReal)) zero_lt_one
  have h_fact := hP.factorial_smul 1 k
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod, Finset.prod_const_one, one_smul] at h_fact
  rw [← Nat.cast_smul_eq_nsmul ℂ] at h_fact
  have h_ne : ((k.factorial : ℝ) : ℂ) ≠ 0 := by
    push_cast
    exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have h_fact2 : (k.factorial : ℂ)⁻¹ • ((k.factorial : ℂ) • cauchyPowerSeries g 0 1 k (fun _ ↦ 1)) =
      (k.factorial : ℂ)⁻¹ • iteratedDeriv k g 0 := by
    rw [h_fact]
  rw [inv_smul_smul₀ (by exact_mod_cast Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k))] at h_fact2
  rw [smul_eq_mul] at h_fact2
  push_cast
  exact h_fact2

lemma vladimirov_iter_psi_schwartz_zero (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z y : Fin n → Fin 4 → ℂ) :
    vladimirov_iter_psi_schwartz n R hR z y 0 = vladimirov_psi_schwartz n R hR z := by
  ext p
  dsimp [vladimirov_iter_psi_schwartz, HasCompactSupport.toSchwartzMap,
    vladimirov_psi_schwartz, vladimirov_iter_psi]
  simp only [pow_zero, one_mul]

lemma vladimirov_iter_psi_schwartz_one (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z y : Fin n → Fin 4 → ℂ) :
    vladimirov_iter_psi_schwartz n R hR z y 1 = vladimirov_deriv_psi_schwartz n R hR z y := by
  ext p
  dsimp [vladimirov_iter_psi_schwartz, HasCompactSupport.toSchwartzMap, vladimirov_iter_psi]
  simp only [pow_one]
  rfl

lemma vladimirov_phase_clm_pow_temperate (n : ℕ) (y : Fin n → Fin 4 → ℂ) (m : ℕ) :
    Function.HasTemperateGrowth
      (fun p : Fin n → Fin 4 → ℝ => (vladimirov_phase_CLM n y p) ^ m) := by
  have h1 : Function.HasTemperateGrowth (vladimirov_phase_CLM n y) :=
    ContinuousLinearMap.hasTemperateGrowth (vladimirov_phase_CLM n y)
  exact h1.pow m

lemma smulLeftCLM_vladimirov_psi_eq_iter_psi (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z y : Fin n → Fin 4 → ℂ) (m : ℕ) :
    SchwartzMap.smulLeftCLM ℂ (fun p => (vladimirov_phase_CLM n y p) ^ m)
      (vladimirov_psi_schwartz n R hR z) =
      vladimirov_iter_psi_schwartz n R hR z y m := by
  have h_temp := vladimirov_phase_clm_pow_temperate n y m
  ext p
  rw [SchwartzMap.smulLeftCLM_apply_apply h_temp]
  dsimp [vladimirov_iter_psi_schwartz, HasCompactSupport.toSchwartzMap,
    vladimirov_iter_psi, vladimirov_psi_schwartz]
  rfl

lemma smulLeftCLM_vladimirov_deriv_psi_eq_iter_psi (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z y : Fin n → Fin 4 → ℂ) (m : ℕ) :
    SchwartzMap.smulLeftCLM ℂ (fun p => (vladimirov_phase_CLM n y p) ^ m)
      (vladimirov_iter_psi_schwartz n R hR z y 1) =
      vladimirov_iter_psi_schwartz n R hR z y (m + 1) := by
  have h_temp := vladimirov_phase_clm_pow_temperate n y m
  ext p
  rw [SchwartzMap.smulLeftCLM_apply_apply h_temp]
  change (vladimirov_phase_CLM n y p) ^ m *
      (vladimirov_iter_psi n R hR z y 1 p) =
    vladimirov_iter_psi n R hR z y (m + 1) p
  dsimp [vladimirov_iter_psi]
  rw [pow_succ]
  ring

lemma vladimirov_slice_hasDerivAt_zero (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z y : Fin n → Fin 4 → ℂ) (T : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ →L[ℂ] ℂ) :
    HasDerivAt (fun t : ℂ => T (vladimirov_psi_schwartz n R hR (z + t • y)))
      (T (vladimirov_iter_psi_schwartz n R hR z y 1)) 0 := by
  rw [vladimirov_iter_psi_schwartz_one]
  have hF : HasFDerivAt (fun w => T (vladimirov_psi_schwartz n R hR w))
      (vladimirov_deriv_T_CLM n R hR z T) z :=
    vladimirov_hasFDerivAt_schwartz_family n R hR z T
  have hL : HasDerivAt (fun t : ℂ => z + t • y) y 0 := by
    have h1 : HasDerivAt (fun t : ℂ => t • y) y 0 := by
      simpa using (hasDerivAt_id' (0 : ℂ)).smul_const y
    have h2 := h1.const_add z
    exact h2
  have h_comp := HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℂ) hF hL (by simp)
  rw [vladimirov_deriv_T_CLM_apply] at h_comp
  exact h_comp

lemma vladimirov_iter_psi_slice_hasDerivAt_zero (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z y : Fin n → Fin 4 → ℂ) (T : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ →L[ℂ] ℂ) (m : ℕ) :
    HasDerivAt (fun t : ℂ => T (vladimirov_iter_psi_schwartz n R hR (z + t • y) y m))
      (T (vladimirov_iter_psi_schwartz n R hR z y (m + 1))) 0 := by
  let Tm : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ →L[ℂ] ℂ :=
    T.comp (SchwartzMap.smulLeftCLM ℂ (fun p => (vladimirov_phase_CLM n y p) ^ m))
  have h_deriv := vladimirov_slice_hasDerivAt_zero n R hR z y Tm
  have h_eq1 : (fun t : ℂ => Tm (vladimirov_psi_schwartz n R hR (z + t • y))) =
      fun t : ℂ => T (vladimirov_iter_psi_schwartz n R hR (z + t • y) y m) := by
    ext t
    dsimp [Tm]
    rw [smulLeftCLM_vladimirov_psi_eq_iter_psi]
  have h_eq2 : Tm (vladimirov_iter_psi_schwartz n R hR z y 1) =
      T (vladimirov_iter_psi_schwartz n R hR z y (m + 1)) := by
    dsimp [Tm]
    rw [smulLeftCLM_vladimirov_deriv_psi_eq_iter_psi]
  rw [h_eq1] at h_deriv
  rw [h_eq2] at h_deriv
  exact h_deriv

lemma vladimirov_iter_psi_slice_hasDerivAt (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z y : Fin n → Fin 4 → ℂ) (T : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ →L[ℂ] ℂ) (m : ℕ) (t : ℂ) :
    HasDerivAt (fun s : ℂ => T (vladimirov_iter_psi_schwartz n R hR (z + s • y) y m))
      (T (vladimirov_iter_psi_schwartz n R hR (z + t • y) y (m + 1))) t := by
  have h0 := vladimirov_iter_psi_slice_hasDerivAt_zero n R hR (z + t • y) y T m
  have h_arg : ∀ s : ℂ, (z + t • y) + (s - t) • y = z + s • y := by
    intro s
    rw [add_assoc, ← add_smul, add_comm t, sub_add_cancel]
  have h_comp :
      (fun s : ℂ =>
        (fun s' : ℂ =>
          T (vladimirov_iter_psi_schwartz n R hR ((z + t • y) + s' • y) y m)) (s - t)) =
      fun s : ℂ => T (vladimirov_iter_psi_schwartz n R hR (z + s • y) y m) := by
    ext s
    dsimp only
    rw [h_arg s]
  rw [← h_comp]
  have h_sub := HasDerivAt.comp_sub_const t t (by rwa [sub_self])
  exact h_sub

lemma vladimirov_iter_psi_slice_deriv (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z y : Fin n → Fin 4 → ℂ) (T : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ →L[ℂ] ℂ) (m : ℕ) :
    deriv (fun s : ℂ => T (vladimirov_iter_psi_schwartz n R hR (z + s • y) y m)) =
      fun t : ℂ => T (vladimirov_iter_psi_schwartz n R hR (z + t • y) y (m + 1)) := by
  ext t
  exact (vladimirov_iter_psi_slice_hasDerivAt n R hR z y T m t).deriv

lemma vladimirov_iter_psi_slice_iteratedDeriv (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z y : Fin n → Fin 4 → ℂ) (T : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ →L[ℂ] ℂ) (k m : ℕ) :
    iteratedDeriv k (fun t : ℂ => T (vladimirov_iter_psi_schwartz n R hR (z + t • y) y m)) 0 =
      T (vladimirov_iter_psi_schwartz n R hR z y (m + k)) := by
  induction k generalizing m with
  | zero =>
    simp only [iteratedDeriv_zero, add_zero]
    change (fun t : ℂ => T (vladimirov_iter_psi_schwartz n R hR (z + t • y) y m)) 0 = _
    simp only [zero_smul, add_zero]
  | succ k ih =>
    rw [iteratedDeriv_succ']
    rw [vladimirov_iter_psi_slice_deriv]
    have h_idx : (m + 1) + k = m + (k + 1) := by omega
    rw [← h_idx]
    exact ih (m + 1)

lemma vladimirov_slice_iteratedDeriv_zero (n : ℕ) (_hn : ¬ n ≤ 1) (R : ℝ) (hR : 0 < R)
    (z y : Fin n → Fin 4 → ℂ) (T : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ →L[ℂ] ℂ) (k : ℕ) :
    iteratedDeriv k (fun t : ℂ => T (vladimirov_psi_schwartz n R hR (z + t • y))) 0 =
      T (vladimirov_iter_psi_schwartz n R hR z y k) := by
  have h_zero : (fun t : ℂ => T (vladimirov_psi_schwartz n R hR (z + t • y))) =
      fun t : ℂ => T (vladimirov_iter_psi_schwartz n R hR (z + t • y) y 0) := by
    ext t
    rw [vladimirov_iter_psi_schwartz_zero]
  rw [h_zero]
  have h_iter := vladimirov_iter_psi_slice_iteratedDeriv n R hR z y T k 0
  rw [zero_add] at h_iter
  exact h_iter

lemma vladimirov_cauchy_coeff_eq_taylor_coeff (n : ℕ) (hn : ¬ n ≤ 1) (R : ℝ) (hR : 0 < R)
    (z y : Fin n → Fin 4 → ℂ) (T : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ →L[ℂ] ℂ) (k : ℕ) :
    (cauchyPowerSeries (fun t : ℂ => T (vladimirov_psi_schwartz n R hR (z + t • y))) 0 1)
        k (fun _ => 1) =
      (vladimirov_formal_series n R hR z T) k (fun _ => y) := by
  let g := fun t : ℂ => T (vladimirov_psi_schwartz n R hR (z + t • y))
  have hg : Differentiable ℂ g := vladimirov_slice_differentiable n hn R hR z y T
  rw [cauchyPowerSeries_one_eq_iteratedDeriv g hg k]
  rw [vladimirov_formal_series_apply]
  dsimp [vladimirov_taylor_coeff]
  congr 1
  exact vladimirov_slice_iteratedDeriv_zero n hn R hR z y T k

lemma vladimirov_formal_series_hasSum (n : ℕ) (hn : ¬ n ≤ 1) (R : ℝ) (hR : 0 < R)
    (z : Fin n → Fin 4 → ℂ) (T : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ →L[ℂ] ℂ)
    (r : ENNReal) (hr_le : r ≤ (vladimirov_formal_series n R hR z T).radius)
    {y : Fin n → Fin 4 → ℂ} (hy : y ∈ Metric.eball (0 : Fin n → Fin 4 → ℂ) r) :
    HasSum (fun k => (vladimirov_formal_series n R hR z T) k (fun _ => y))
      (T (vladimirov_psi_schwartz n R hR (z + y))) := by
  let p := vladimirov_formal_series n R hR z T
  have hy_p : y ∈ Metric.eball (0 : Fin n → Fin 4 → ℂ) p.radius :=
    Metric.eball_subset_eball hr_le hy
  have h_sum := p.hasSum hy_p
  have h_eq : p.sum y = T (vladimirov_psi_schwartz n R hR (z + y)) := by
    rw [vladimirov_slice_eval_eq_sum n hn R hR z y T]
    have h_coeff : ∀ k,
        (cauchyPowerSeries (fun t : ℂ => T (vladimirov_psi_schwartz n R hR (z + t • y))) 0 1)
          k (fun _ => 1) = p k (fun _ => y) :=
      fun k => vladimirov_cauchy_coeff_eq_taylor_coeff n hn R hR z y T k
    dsimp [FormalMultilinearSeries.sum]
    refine tsum_congr (fun k => (h_coeff k).symm)
  rw [← h_eq]
  exact h_sum

lemma vladimirov_psi_schwartz_analyticAt (n : ℕ) (hn : ¬ n ≤ 1) (R : ℝ) (hR : 0 < R)
    (z : Fin n → Fin 4 → ℂ) (T : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ →L[ℂ] ℂ) :
    AnalyticAt ℂ (fun w => T (vladimirov_psi_schwartz n R hR w)) z := by
  let p := vladimirov_formal_series n R hR z T
  have h_pos := vladimirov_formal_series_radius_pos n R hR z T
  use p
  use p.radius
  refine ⟨le_rfl, h_pos, ?_⟩
  intro y hy
  exact vladimirov_formal_series_hasSum n hn R hR z T p.radius le_rfl hy

lemma vladimirov_psi_schwartz_family_analyticAt (n : ℕ) (hn : ¬ n ≤ 1) (R : ℝ) (hR : 0 < R)
    (z : Fin n → Fin 4 → ℂ) :
    SchwartzFamilyAnalyticAt n R hR z := by
  intro T
  exact vladimirov_psi_schwartz_analyticAt n hn R hR z T

end VladimirovMultilinearAnalytic

lemma vladimirov_H_analytic_at (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (hspec : SpectrumCondition W) (hP : PoincareCovariant R W) (n : ℕ) (α : Fin n → ι)
    (z : Fin n → Fin 4 → ℂ) (hz : z ∈ forward_tube_n n) :
    AnalyticAt ℂ (vladimirov_H W n α) z := by
  by_cases hn : n ≤ 1
  · interval_cases n
    · exact vladimirov_H_analytic_at_zero W α z
    · exact vladimirov_H_analytic_at_one R W hP α z hz
        (fun f' => W_one_eq_integral R W hspec hP α f')
  · apply vladimirov_H_analyticAt_of_family
    exact vladimirov_psi_schwartz_family_analyticAt n hn 1 Real.zero_lt_one z

lemma vladimirov_H_analytic (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (hspec : SpectrumCondition W) (hP : PoincareCovariant R W) (n : ℕ) (α : Fin n → ι) :
    AnalyticOn ℂ (vladimirov_H W n α) (forward_tube_n n) := by
  cases n with
  | zero => exact vladimirov_H_analytic_zero W α
  | succ m =>
    rw [vladimirov_H_analyticOn_iff]
    intro z hz
    exact vladimirov_H_analytic_at R W hspec hP (m + 1) α z hz

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_H_boundary_pointwise_limit (n : ℕ)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) (p : Fin n → Fin 4 → ℝ)
    (v : Fin 4 → ℝ) :
    Tendsto (fun t : ℝ => ∫ x : Fin n → Fin 4 → ℝ, f x * vladimirov_psi n 1 Real.zero_lt_one
        (fun i k => (x i k : ℂ) + Complex.I * ((t * ((i : ℕ) : ℝ) * v k : ℝ) : ℂ)) p)
      (𝓝[>] 0)
      (𝓝 (((vladimirovCutoffBump n 1 Real.zero_lt_one p : ℝ) : ℂ) * minkowskiFourier f p)) :=
  tendsto_integral_f_mul_vladimirov_psi n 1 Real.zero_lt_one f p v

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_H_boundary_integrand_comm (W : WightmanFamily ι) (n : ℕ) (α : Fin n → ι)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) (t : ℝ) (v : Fin 4 → ℝ)
    (x : Fin n → Fin 4 → ℝ) :
    vladimirov_H W n α (fun i k => (x i k : ℂ) +
      Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ)) * f x =
    f x * vladimirov_H W n α (fun i k => (x i k : ℂ) +
      Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ)) :=
  mul_comm _ _

omit [Fintype ι] [DecidableEq ι] in
lemma tendsto_of_sub_tendsto_zero {α : Type*} {E : Type*} [NormedAddCommGroup E]
    (F : α → E) (L : E) (l : Filter α)
    (h : Tendsto (fun a => F a - L) l (𝓝 0)) :
    Tendsto F l (𝓝 L) := by
  have h_add := Tendsto.add h (tendsto_const_nhds (x := L))
  simp only [sub_add_cancel, zero_add] at h_add
  exact h_add

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_H_analyticAt_entire (W : WightmanFamily ι)
    (n : ℕ) (hn : ¬ n ≤ 1) (α : Fin n → ι)
    (z : Fin n → Fin 4 → ℂ) :
    AnalyticAt ℂ (vladimirov_H W n α) z := by
  apply vladimirov_H_analyticAt_of_family
  exact vladimirov_psi_schwartz_family_analyticAt n hn 1 Real.zero_lt_one z

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_H_continuous (W : WightmanFamily ι)
    (n : ℕ) (hn : ¬ n ≤ 1) (α : Fin n → ι) :
    Continuous (vladimirov_H W n α) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  exact (vladimirov_H_analyticAt_entire W n hn α z).continuousAt

omit [Fintype ι] [DecidableEq ι] in
lemma tendsto_vladimirov_H_pointwise (W : WightmanFamily ι)
    (n : ℕ) (hn : ¬ n ≤ 1) (α : Fin n → ι)
    (x : Fin n → Fin 4 → ℝ) (v : Fin 4 → ℝ) :
    Tendsto (fun t : ℝ => vladimirov_H W n α
        (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ)))
      (𝓝[>] 0)
      (𝓝 (vladimirov_H W n α (fun i k => (x i k : ℂ)))) := by
  have h_cont := (vladimirov_H_continuous W n hn α).continuousAt
    (x := fun i k => (x i k : ℂ))
  have h_shift : Tendsto (fun t : ℝ =>
      (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ)))
      (𝓝[>] 0)
      (𝓝 (fun i k => (x i k : ℂ))) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro k
    have h_eval : Tendsto (fun t : ℝ =>
        (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ))
        (𝓝[>] 0)
        (𝓝 ((x i k : ℂ) + Complex.I * ((0 * (i : ℕ) * v k : ℝ) : ℂ))) := by
      refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
      refine tendsto_const_nhds.add (tendsto_const_nhds.mul ?_)
      have h_cont_t : Continuous (fun t : ℝ => ((t * ((i : ℕ) : ℝ) * v k : ℝ) : ℂ)) := by
        exact Complex.continuous_ofReal.comp
          ((continuous_id.mul continuous_const).mul continuous_const)
      exact h_cont_t.tendsto 0
    simp only [MulZeroClass.zero_mul, Complex.ofReal_zero, mul_zero, add_zero] at h_eval
    exact h_eval
  exact Tendsto.comp h_cont h_shift

omit [Fintype ι] [DecidableEq ι] in
lemma tendsto_vladimirov_H_mul_f_pointwise (W : WightmanFamily ι)
    (n : ℕ) (hn : ¬ n ≤ 1) (α : Fin n → ι)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    (x : Fin n → Fin 4 → ℝ) (v : Fin 4 → ℝ) :
    Tendsto (fun t : ℝ => vladimirov_H W n α
        (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ)) * f x)
      (𝓝[>] 0)
      (𝓝 (vladimirov_H W n α (fun i k => (x i k : ℂ)) * f x)) :=
  (tendsto_vladimirov_H_pointwise W n hn α x v).mul tendsto_const_nhds

omit [Fintype ι] [DecidableEq ι] in
lemma continuous_vladimirov_H_integrand (W : WightmanFamily ι)
    (n : ℕ) (hn : ¬ n ≤ 1) (α : Fin n → ι)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    (t : ℝ) (v : Fin 4 → ℝ) :
    Continuous (fun x : Fin n → Fin 4 → ℝ =>
      vladimirov_H W n α
        (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ)) * f x) := by
  apply Continuous.mul
  · have h_H := vladimirov_H_continuous W n hn α
    have h_arg : Continuous (fun x : Fin n → Fin 4 → ℝ =>
        (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ))) := by
      apply continuous_pi
      intro i
      apply continuous_pi
      intro k
      refine Continuous.add ?_ continuous_const
      exact Complex.continuous_ofReal.comp
        ((continuous_apply k).comp (continuous_apply i))
    exact h_H.comp h_arg
  · exact f.continuous

omit [Fintype ι] [DecidableEq ι] in
lemma aestronglyMeasurable_vladimirov_H_integrand (W : WightmanFamily ι)
    (n : ℕ) (hn : ¬ n ≤ 1) (α : Fin n → ι)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    (t : ℝ) (v : Fin 4 → ℝ) :
    AEStronglyMeasurable (fun x : Fin n → Fin 4 → ℝ =>
      vladimirov_H W n α
        (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ)) * f x)
      volume :=
  (continuous_vladimirov_H_integrand W n hn α f t v).aestronglyMeasurable

omit [Fintype ι] [DecidableEq ι] in
lemma W_vanish_of_fourier_zero (W : WightmanFamily ι)
    (hspec : SpectrumCondition W) (n : ℕ) (α : Fin n → ι)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    (U : Set (Fin n → Fin 4 → ℝ)) (hU : IsOpen U)
    (h_sub : spectralRegion n ⊆ U)
    (hf : ∀ p ∈ U, minkowskiFourier f p = 0) :
    W n α f = 0 :=
  hspec n α f (Or.inl ⟨U, hU, h_sub, hf⟩)

omit [Fintype ι] [DecidableEq ι] in
lemma W_eq_of_fourier_eq (W : WightmanFamily ι)
    (hspec : SpectrumCondition W) (n : ℕ) (α : Fin n → ι)
    (f g : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    (U : Set (Fin n → Fin 4 → ℝ)) (hU : IsOpen U)
    (h_sub : spectralRegion n ⊆ U)
    (hfg : ∀ p ∈ U, minkowskiFourier f p = minkowskiFourier g p) :
    W n α f = W n α g := by
  have h_diff : W n α f - W n α g = W n α (f - g) := (map_sub (W n α) f g).symm
  rw [← sub_eq_zero, h_diff]
  apply W_vanish_of_fourier_zero W hspec n α (f - g) U hU h_sub
  intro p hp
  rw [minkowskiFourier_sub]
  rw [hfg p hp, sub_self]

omit [Fintype ι] [DecidableEq ι] in
lemma tendsto_sub_zero_of_tendsto_and_eq {α : Type*} {E : Type*} [NormedAddCommGroup E]
    (F : α → E) (L L' : E) (l : Filter α)
    (h_tend : Tendsto F l (𝓝 L))
    (h_eq : L = L') :
    Tendsto (fun a => F a - L') l (𝓝 0) := by
  rw [← h_eq]
  have h_sub := Tendsto.sub h_tend (tendsto_const_nhds (x := L))
  rw [sub_self] at h_sub
  exact h_sub

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_cutoff_mul_fourier_eq_on_ball (n : ℕ)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    (p : Fin n → Fin 4 → ℝ) (hp : p ∈ Metric.ball (0 : Fin n → Fin 4 → ℝ) 1) :
    ((vladimirovCutoffBump n 1 Real.zero_lt_one p : ℝ) : ℂ) * minkowskiFourier f p =
    minkowskiFourier f p := by
  have h_bump : (vladimirovCutoffBump n 1 Real.zero_lt_one p : ℝ) = 1 :=
    vladimirov_cutoff_bump_one_of_mem_ball_gen n 1 le_rfl p hp
  rw [h_bump]
  push_cast
  exact one_mul _

noncomputable def vladimirov_boundary_F (n : ℕ) (R : ℝ) (hR : 0 < R)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) (v : Fin 4 → ℝ) (t : ℝ)
    (p : Fin n → Fin 4 → ℝ) : ℂ :=
  ((vladimirovCutoffBump n R hR p : ℝ) : ℂ) *
    (Complex.exp (t * ∑ k : Fin n, ((k : ℕ) : ℝ) * minkowskiInner (p k) v : ℂ) *
      minkowskiFourier f p)

lemma vladimirov_boundary_F_eq_integral (n : ℕ) (R : ℝ) (hR : 0 < R)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) (v : Fin 4 → ℝ) (t : ℝ)
    (p : Fin n → Fin 4 → ℝ) :
    vladimirov_boundary_F n R hR f v t p =
    ∫ x : Fin n → Fin 4 → ℝ, f x * vladimirov_psi n R hR
        (fun i k => (x i k : ℂ) + Complex.I * ((t * ((i : ℕ) : ℝ) * v k : ℝ) : ℂ)) p := by
  dsimp [vladimirov_boundary_F]
  rw [integral_f_mul_vladimirov_psi n R hR f p v t]

lemma vladimirov_boundary_F_zero (n : ℕ) (R : ℝ) (hR : 0 < R)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) (v : Fin 4 → ℝ)
    (p : Fin n → Fin 4 → ℝ) :
    vladimirov_boundary_F n R hR f v 0 p =
    ((vladimirovCutoffBump n R hR p : ℝ) : ℂ) * minkowskiFourier f p := by
  dsimp [vladimirov_boundary_F]
  simp only [MulZeroClass.zero_mul, Complex.exp_zero, one_mul]

lemma tendsto_vladimirov_boundary_F (n : ℕ) (R : ℝ) (hR : 0 < R)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) (v : Fin 4 → ℝ)
    (p : Fin n → Fin 4 → ℝ) :
    Tendsto (fun t : ℝ => vladimirov_boundary_F n R hR f v t p)
      (𝓝[>] 0)
      (𝓝 (((vladimirovCutoffBump n R hR p : ℝ) : ℂ) * minkowskiFourier f p)) := by
  have h_eq : (fun t : ℝ => vladimirov_boundary_F n R hR f v t p) =
      (fun t : ℝ => ∫ x : Fin n → Fin 4 → ℝ, f x * vladimirov_psi n R hR
          (fun i k => (x i k : ℂ) + Complex.I * ((t * ((i : ℕ) : ℝ) * v k : ℝ) : ℂ)) p) := by
    ext t
    rw [vladimirov_boundary_F_eq_integral]
  rw [h_eq]
  exact tendsto_integral_f_mul_vladimirov_psi n R hR f p v

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_H_boundary_weak_convergence_sub_zero_of_integral_zero
    (W : WightmanFamily ι) (n : ℕ) (_hn : ¬ n ≤ 1) (α : Fin n → ι)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    (v : Fin 4 → ℝ) (_hv : v ∈ (forward_light_cone : Set (Fin 4 → ℝ)))
    (h_tend_real : Tendsto (fun t : ℝ => ∫ x : Fin n → Fin 4 → ℝ,
        vladimirov_H W n α
          (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ)) * f x)
      (𝓝[>] 0) (𝓝 (∫ x : Fin n → Fin 4 → ℝ,
        vladimirov_H W n α (fun i k => (x i k : ℂ)) * f x)))
    (h_real_eq : (∫ x : Fin n → Fin 4 → ℝ,
        vladimirov_H W n α (fun i k => (x i k : ℂ)) * f x) = W n α f) :
    Tendsto (fun t : ℝ => (∫ x : Fin n → Fin 4 → ℝ,
        vladimirov_H W n α
          (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ)) * f x) -
        W n α f)
      (𝓝[>] 0) (𝓝 0) := by
  have h_conv : Tendsto (fun t : ℝ => ∫ x : Fin n → Fin 4 → ℝ,
      vladimirov_H W n α
        (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ)) * f x)
    (𝓝[>] 0) (𝓝 (W n α f)) := by
    rw [← h_real_eq]
    exact h_tend_real
  exact tendsto_sub_zero_of_tendsto_and_eq _ (W n α f) (W n α f) (𝓝[>] 0) h_conv rfl

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_H_boundary_step_of_real_limit
    (W : WightmanFamily ι) (n : ℕ) (_hn : ¬ n ≤ 1) (α : Fin n → ι)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    (v : Fin 4 → ℝ) (_hv : v ∈ (forward_light_cone : Set (Fin 4 → ℝ)))
    (h_tend_real : Tendsto (fun t : ℝ => ∫ x : Fin n → Fin 4 → ℝ,
        vladimirov_H W n α
          (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ)) * f x)
      (𝓝[>] 0) (𝓝 (∫ x : Fin n → Fin 4 → ℝ,
        vladimirov_H W n α (fun i k => (x i k : ℂ)) * f x)))
    (h_real_eq : (∫ x : Fin n → Fin 4 → ℝ,
        vladimirov_H W n α (fun i k => (x i k : ℂ)) * f x) = W n α f) :
    Tendsto (fun t : ℝ => ∫ x : Fin n → Fin 4 → ℝ,
        vladimirov_H W n α
          (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ)) * f x)
      (𝓝[>] 0) (𝓝 (W n α f)) := by
  rw [← h_real_eq]
  exact h_tend_real

omit [Fintype ι] [DecidableEq ι] in
lemma test_boundary_weak_convergence_chain
    (W : WightmanFamily ι) (n : ℕ) (_hn : ¬ n ≤ 1) (α : Fin n → ι)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    (v : Fin 4 → ℝ) (_hv : v ∈ (forward_light_cone : Set (Fin 4 → ℝ)))
    (h_sub_zero : Tendsto (fun t : ℝ => (∫ x : Fin n → Fin 4 → ℝ,
        vladimirov_H W n α
          (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ)) * f x) -
        W n α f)
      (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun t : ℝ => ∫ x : Fin n → Fin 4 → ℝ,
        vladimirov_H W n α
          (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ)) * f x)
      (𝓝[>] 0) (𝓝 (W n α f)) :=
  tendsto_of_sub_tendsto_zero _ _ _ h_sub_zero

omit [Fintype ι] [DecidableEq ι] in
lemma test_boundary_weak_limit_chain
    (W : WightmanFamily ι) (n : ℕ) (_hn : ¬ n ≤ 1) (α : Fin n → ι)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    (v : Fin 4 → ℝ) (_hv : v ∈ (forward_light_cone : Set (Fin 4 → ℝ)))
    (h_conv : Tendsto (fun t : ℝ => ∫ x : Fin n → Fin 4 → ℝ,
        vladimirov_H W n α
          (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ)) * f x)
      (𝓝[>] 0) (𝓝 (W n α f))) :
    ∃ L : ℂ,
      Tendsto (fun t : ℝ => ∫ x : Fin n → Fin 4 → ℝ,
          vladimirov_H W n α
            (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ)) * f x)
        (𝓝[>] 0) (𝓝 L) ∧
      L = W n α f :=
  ⟨W n α f, h_conv, rfl⟩

lemma test_boundary_step_chain (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (_hspec : SpectrumCondition W) (_hP : PoincareCovariant R W) (n : ℕ) (_hn : ¬ n ≤ 1)
    (α : Fin n → ι) (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    (v : Fin 4 → ℝ) (_hv : v ∈ (forward_light_cone : Set (Fin 4 → ℝ)))
    (h_lim : ∃ L : ℂ,
      Tendsto (fun t : ℝ => ∫ x : Fin n → Fin 4 → ℝ,
          vladimirov_H W n α
            (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ)) * f x)
        (𝓝[>] 0) (𝓝 L) ∧
      L = W n α f) :
    Tendsto (fun t : ℝ => ∫ x : Fin n → Fin 4 → ℝ,
        vladimirov_H W n α
          (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ)) * f x)
      (𝓝[>] 0) (𝓝 (W n α f)) := by
  obtain ⟨L, h_tend, h_eq⟩ := h_lim
  rw [h_eq] at h_tend
  exact h_tend

omit [Fintype ι] [DecidableEq ι] in
lemma W_eq_of_cutoff_fourier_eq_on_ball (W : WightmanFamily ι)
    (hspec : SpectrumCondition W) (n : ℕ) (α : Fin n → ι)
    (f g : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    (U : Set (Fin n → Fin 4 → ℝ)) (hU : IsOpen U)
    (h_sub : spectralRegion n ⊆ U)
    (hU_ball : U ⊆ Metric.ball 0 1)
    (hfg : ∀ p ∈ U, minkowskiFourier g p =
      ((vladimirovCutoffBump n 1 Real.zero_lt_one p : ℝ) : ℂ) * minkowskiFourier f p) :
    W n α g = W n α f := by
  apply W_eq_of_fourier_eq W hspec n α g f U hU h_sub
  intro p hp
  rw [hfg p hp]
  have hp_ball : p ∈ Metric.ball 0 1 := hU_ball hp
  exact vladimirov_cutoff_mul_fourier_eq_on_ball n f p hp_ball

omit [Fintype ι] [DecidableEq ι] in
lemma W_eq_of_boundary_F_zero (W : WightmanFamily ι)
    (hspec : SpectrumCondition W) (n : ℕ) (α : Fin n → ι)
    (f g : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    (v : Fin 4 → ℝ)
    (U : Set (Fin n → Fin 4 → ℝ)) (hU : IsOpen U)
    (h_sub : spectralRegion n ⊆ U)
    (hU_ball : U ⊆ Metric.ball 0 1)
    (hfg : ∀ p ∈ U, minkowskiFourier g p =
      vladimirov_boundary_F n 1 Real.zero_lt_one f v 0 p) :
    W n α g = W n α f := by
  apply W_eq_of_cutoff_fourier_eq_on_ball W hspec n α f g U hU h_sub hU_ball
  intro p hp
  rw [hfg p hp]
  exact vladimirov_boundary_F_zero n 1 Real.zero_lt_one f v p

omit [Fintype ι] [DecidableEq ι] in
lemma tendsto_vladimirov_boundary_F_on_ball (n : ℕ)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) (v : Fin 4 → ℝ)
    (p : Fin n → Fin 4 → ℝ) (hp : p ∈ Metric.ball (0 : Fin n → Fin 4 → ℝ) 1) :
    Tendsto (fun t : ℝ => vladimirov_boundary_F n 1 Real.zero_lt_one f v t p)
      (𝓝[>] 0)
      (𝓝 (minkowskiFourier f p)) := by
  have h_tend := tendsto_vladimirov_boundary_F n 1 Real.zero_lt_one f v p
  have h_eq := vladimirov_cutoff_mul_fourier_eq_on_ball n f p hp
  rw [← h_eq]
  exact h_tend

lemma vladimirov_boundary_F_zero_eq_integral (n : ℕ)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) (v : Fin 4 → ℝ)
    (p : Fin n → Fin 4 → ℝ) :
    vladimirov_boundary_F n 1 Real.zero_lt_one f v 0 p =
    ∫ x : Fin n → Fin 4 → ℝ, f x * vladimirov_psi n 1 Real.zero_lt_one
        (fun i k => (x i k : ℂ)) p := by
  rw [vladimirov_boundary_F_eq_integral]
  congr 1
  ext x
  congr 1
  congr 1
  ext i k
  simp only [MulZeroClass.zero_mul, Complex.ofReal_zero, mul_zero, add_zero]

lemma integral_f_mul_psi_real_eq_fourier_on_ball (n : ℕ)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) (v : Fin 4 → ℝ)
    (p : Fin n → Fin 4 → ℝ) (hp : p ∈ Metric.ball (0 : Fin n → Fin 4 → ℝ) 1) :
    (∫ x : Fin n → Fin 4 → ℝ, f x * vladimirov_psi n 1 Real.zero_lt_one
        (fun i k => (x i k : ℂ)) p) = minkowskiFourier f p := by
  rw [← vladimirov_boundary_F_zero_eq_integral n f v p]
  rw [vladimirov_boundary_F_zero]
  exact vladimirov_cutoff_mul_fourier_eq_on_ball n f p hp

omit [Fintype ι] [DecidableEq ι] in
lemma W_eq_of_integral_psi_eq_on_ball (W : WightmanFamily ι)
    (hspec : SpectrumCondition W) (n : ℕ) (α : Fin n → ι)
    (f g : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) (v : Fin 4 → ℝ)
    (U : Set (Fin n → Fin 4 → ℝ)) (hU : IsOpen U)
    (h_sub : spectralRegion n ⊆ U)
    (hU_ball : U ⊆ Metric.ball 0 1)
    (hfg : ∀ p ∈ U, minkowskiFourier g p =
      ∫ x : Fin n → Fin 4 → ℝ, f x * vladimirov_psi n 1 Real.zero_lt_one
        (fun i k => (x i k : ℂ)) p) :
    W n α g = W n α f := by
  apply W_eq_of_fourier_eq W hspec n α g f U hU h_sub
  intro p hp
  rw [hfg p hp]
  have hp_ball : p ∈ Metric.ball 0 1 := hU_ball hp
  exact integral_f_mul_psi_real_eq_fourier_on_ball n f v p hp_ball

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_H_boundary_weak_convergence_sub_zero
    (W : WightmanFamily ι) (n : ℕ) (hn : ¬ n ≤ 1) (α : Fin n → ι)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    (v : Fin 4 → ℝ) (hv : v ∈ (forward_light_cone : Set (Fin 4 → ℝ)))
    (h_tend_real : Tendsto (fun t : ℝ => ∫ x : Fin n → Fin 4 → ℝ,
        vladimirov_H W n α
          (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ)) * f x)
      (𝓝[>] 0) (𝓝 (∫ x : Fin n → Fin 4 → ℝ,
        vladimirov_H W n α (fun i k => (x i k : ℂ)) * f x)))
    (h_real_eq : (∫ x : Fin n → Fin 4 → ℝ,
        vladimirov_H W n α (fun i k => (x i k : ℂ)) * f x) = W n α f) :
    Tendsto (fun t : ℝ => (∫ x : Fin n → Fin 4 → ℝ,
        vladimirov_H W n α
          (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ)) * f x) -
        W n α f)
      (𝓝[>] 0) (𝓝 0) :=
  vladimirov_H_boundary_weak_convergence_sub_zero_of_integral_zero W n hn α f v hv
    h_tend_real h_real_eq

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_H_boundary_weak_convergence
    (W : WightmanFamily ι) (n : ℕ) (hn : ¬ n ≤ 1) (α : Fin n → ι)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    (v : Fin 4 → ℝ) (hv : v ∈ (forward_light_cone : Set (Fin 4 → ℝ)))
    (h_tend_real : Tendsto (fun t : ℝ => ∫ x : Fin n → Fin 4 → ℝ,
        vladimirov_H W n α
          (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ)) * f x)
      (𝓝[>] 0) (𝓝 (∫ x : Fin n → Fin 4 → ℝ,
        vladimirov_H W n α (fun i k => (x i k : ℂ)) * f x)))
    (h_real_eq : (∫ x : Fin n → Fin 4 → ℝ,
        vladimirov_H W n α (fun i k => (x i k : ℂ)) * f x) = W n α f) :
    Tendsto (fun t : ℝ => ∫ x : Fin n → Fin 4 → ℝ,
        vladimirov_H W n α
          (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ)) * f x)
      (𝓝[>] 0) (𝓝 (W n α f)) :=
  tendsto_of_sub_tendsto_zero _ _ _
    (vladimirov_H_boundary_weak_convergence_sub_zero W n hn α f v hv h_tend_real h_real_eq)

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_H_boundary_weak_limit
    (W : WightmanFamily ι) (n : ℕ) (hn : ¬ n ≤ 1) (α : Fin n → ι)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    (v : Fin 4 → ℝ) (hv : v ∈ (forward_light_cone : Set (Fin 4 → ℝ)))
    (h_tend_real : Tendsto (fun t : ℝ => ∫ x : Fin n → Fin 4 → ℝ,
        vladimirov_H W n α
          (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ)) * f x)
      (𝓝[>] 0) (𝓝 (∫ x : Fin n → Fin 4 → ℝ,
        vladimirov_H W n α (fun i k => (x i k : ℂ)) * f x)))
    (h_real_eq : (∫ x : Fin n → Fin 4 → ℝ,
        vladimirov_H W n α (fun i k => (x i k : ℂ)) * f x) = W n α f) :
    ∃ L : ℂ,
      Tendsto (fun t : ℝ => ∫ x : Fin n → Fin 4 → ℝ,
          vladimirov_H W n α
            (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ)) * f x)
        (𝓝[>] 0) (𝓝 L) ∧
      L = W n α f :=
  ⟨W n α f,
   vladimirov_H_boundary_weak_convergence W n hn α f v hv h_tend_real h_real_eq,
   rfl⟩

lemma vladimirov_H_boundary_step_final (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (_hspec : SpectrumCondition W) (_hP : PoincareCovariant R W) (n : ℕ) (hn : ¬ n ≤ 1)
    (α : Fin n → ι) (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    (v : Fin 4 → ℝ) (hv : v ∈ (forward_light_cone : Set (Fin 4 → ℝ)))
    (h_tend_real : Tendsto (fun t : ℝ => ∫ x : Fin n → Fin 4 → ℝ,
        vladimirov_H W n α
          (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ)) * f x)
      (𝓝[>] 0) (𝓝 (∫ x : Fin n → Fin 4 → ℝ,
        vladimirov_H W n α (fun i k => (x i k : ℂ)) * f x)))
    (h_real_eq : (∫ x : Fin n → Fin 4 → ℝ,
        vladimirov_H W n α (fun i k => (x i k : ℂ)) * f x) = W n α f) :
    Tendsto (fun t : ℝ => ∫ x : Fin n → Fin 4 → ℝ,
        vladimirov_H W n α
          (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ)) * f x)
      (𝓝[>] 0) (𝓝 (W n α f)) := by
  obtain ⟨L, h_tend, h_eq⟩ :=
    vladimirov_H_boundary_weak_limit W n hn α f v hv h_tend_real h_real_eq
  rw [h_eq] at h_tend
  exact h_tend

omit [Fintype ι] [DecidableEq ι] in
lemma close_lorentz_cov_step_general (W : WightmanFamily ι)
    (hspec : SpectrumCondition W)
    (n : ℕ) (α : Fin n → ι)
    (f1 f2 : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    (h_vanish : ∃ U : Set (Fin n → Fin 4 → ℝ), IsOpen U ∧ spectralRegion n ⊆ U ∧
      ∀ p ∈ U, minkowskiFourier (f1 - f2) p = 0) :
    W n α f1 - W n α f2 = 0 := by
  have h_sub : W n α f1 - W n α f2 = W n α (f1 - f2) := by rw [map_sub]
  rw [h_sub]
  exact hspec n α (f1 - f2) (Or.inl h_vanish)

omit [Fintype ι] [DecidableEq ι] in
lemma close_lorentz_cov_step_R (W : WightmanFamily ι)
    (hspec : SpectrumCondition W)
    (n : ℕ) (A : SL2C) (R : ℝ) (hR : 0 < R) (α : Fin n → ι)
    (f1 f2 : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    (h_fourier : ∀ p ∈ scaledComNeighborhood n A R, minkowskiFourier (f1 - f2) p = 0) :
    W n α f1 - W n α f2 = 0 :=
  close_lorentz_cov_step_general W hspec n α f1 f2
    ⟨scaledComNeighborhood n A R,
     isOpen_scaledComNeighborhood n A R,
     spectralRegion_subset_scaledComNeighborhood n A R hR,
     h_fourier⟩

omit [Fintype ι] [DecidableEq ι] in
lemma close_lorentz_cov_step (W : WightmanFamily ι)
    (hspec : SpectrumCondition W)
    (n : ℕ) (A : SL2C) (α : Fin n → ι)
    (f1 f2 : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    (h_fourier : ∀ p ∈ scaledComNeighborhood n A 1, minkowskiFourier (f1 - f2) p = 0) :
    W n α f1 - W n α f2 = 0 :=
  close_lorentz_cov_step_R W hspec n A 1 Real.zero_lt_one α f1 f2 h_fourier

lemma contDiff_scaledMomentumN (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (scaledMomentumN n) := by
  change ContDiff ℝ (⊤ : ℕ∞) (fun p => (- (2 * Real.pi)⁻¹) • p)
  exact contDiff_const_smul _

lemma fourier_invCLM_contDiff (n : ℕ) (g : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p => minkowskiFourier (invMinkowskiFourierCLM n g) p) := by
  have h_eq : (fun p => minkowskiFourier (invMinkowskiFourierCLM n g) p) =
      (fun p => g (scaledMomentumN n p)) := by
    ext p
    exact minkowskiFourier_invMinkowskiFourierCLM_all n g p
  rw [h_eq]
  exact g.smooth'.comp (contDiff_scaledMomentumN n)

lemma vladimirov_cutoff_mul_fourier_invCLM_contDiff (n : ℕ) (R : ℝ) (hR : 0 < R)
    (g : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p => ((vladimirovCutoffBump n R hR p : ℝ) : ℂ) *
      minkowskiFourier (invMinkowskiFourierCLM n g) p) := by
  have h_bump : ContDiff ℝ (⊤ : ℕ∞) (fun p => ((vladimirovCutoffBump n R hR p : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (vladimirovCutoffBump n R hR).contDiff
  exact h_bump.mul (fourier_invCLM_contDiff n g)

lemma vladimirov_cutoff_mul_fourier_invCLM_hasCompactSupport (n : ℕ) (R : ℝ) (hR : 0 < R)
    (g : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    HasCompactSupport (fun p => ((vladimirovCutoffBump n R hR p : ℝ) : ℂ) *
      minkowskiFourier (invMinkowskiFourierCLM n g) p) := by
  have h_supp : HasCompactSupport (fun p => ((vladimirovCutoffBump n R hR p : ℝ) : ℂ)) := by
    have h1 := (vladimirovCutoffBump n R hR).hasCompactSupport
    exact h1.comp_left (g := fun (r : ℝ) => (r : ℂ)) Complex.ofReal_zero
  exact h_supp.mul_right

noncomputable def vladimirov_cutoff_fourier_invCLM_schwartz (n : ℕ) (R : ℝ) (hR : 0 < R)
    (g : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    SchwartzMap (Fin n → Fin 4 → ℝ) ℂ :=
  (vladimirov_cutoff_mul_fourier_invCLM_hasCompactSupport n R hR g).toSchwartzMap
    (vladimirov_cutoff_mul_fourier_invCLM_contDiff n R hR g)

lemma integrable_polynomial_mul_schwartz (n : ℕ) (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    (C : ℝ) (m : ℕ) :
    Integrable (fun x : Fin n → Fin 4 → ℝ => C * (1 + ‖x‖ ^ m) * ‖f x‖) volume := by
  have h1 : Integrable (fun x => C * ‖f x‖) volume := f.integrable.norm.const_mul C
  have h2 : Integrable (fun x => C * (‖x‖ ^ m * ‖f x‖)) volume :=
    (f.integrable_pow_mul volume m).const_mul C
  have h_eq : (fun x => C * (1 + ‖x‖ ^ m) * ‖f x‖) =
      (fun x => C * ‖f x‖ + C * (‖x‖ ^ m * ‖f x‖)) := by
    ext x
    ring
  rw [h_eq]
  exact h1.add h2

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_H_boundary_step_h_tend_real_of_poly (W : WightmanFamily ι) (n : ℕ) (hn : ¬ n ≤ 1)
    (α : Fin n → ι) (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    (v : Fin 4 → ℝ) (_hv : v ∈ (forward_light_cone : Set (Fin 4 → ℝ)))
    (C : ℝ) (m : ℕ)
    (h_bound : ∀ᶠ (t : ℝ) in 𝓝[>] 0, ∀ (x : Fin n → Fin 4 → ℝ),
      ‖vladimirov_H W n α
        (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ))‖ ≤ C * (1 + ‖x‖ ^ m)) :
    Tendsto (fun t : ℝ => ∫ x : Fin n → Fin 4 → ℝ,
        vladimirov_H W n α
          (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ)) * f x)
      (𝓝[>] 0) (𝓝 (∫ x : Fin n → Fin 4 → ℝ,
        vladimirov_H W n α (fun i k => (x i k : ℂ)) * f x)) := by
  let bound : (Fin n → Fin 4 → ℝ) → ℝ := fun x => C * (1 + ‖x‖ ^ m) * ‖f x‖
  have h_bound_integ : Integrable bound volume := integrable_polynomial_mul_schwartz n f C m
  have h_bnd : ∀ᶠ (t : ℝ) in 𝓝[>] 0, ∀ᵐ (x : Fin n → Fin 4 → ℝ),
      ‖vladimirov_H W n α
        (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ)) * f x‖ ≤ bound x := by
    apply h_bound.mono
    intro t ht
    exact ae_of_all _ (fun x => by
      dsimp [bound]
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (ht x) (norm_nonneg _))
  have h_meas : ∀ᶠ (t : ℝ) in 𝓝[>] 0, AEStronglyMeasurable
      (fun x => vladimirov_H W n α
        (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ)) * f x)
      volume :=
    Filter.Eventually.of_forall
      (fun t => aestronglyMeasurable_vladimirov_H_integrand W n hn α f t v)
  have h_lim : ∀ᵐ (x : Fin n → Fin 4 → ℝ), Tendsto
      (fun t : ℝ => vladimirov_H W n α
        (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ)) * f x)
      (𝓝[>] 0)
      (𝓝 (vladimirov_H W n α (fun i k => (x i k : ℂ)) * f x)) :=
    ae_of_all _ (fun x => tendsto_vladimirov_H_mul_f_pointwise W n hn α f x v)
  exact tendsto_integral_filter_of_dominated_convergence bound h_meas h_bnd h_bound_integ h_lim

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_H_boundary_step_h_tend_real_of_const (W : WightmanFamily ι) (n : ℕ) (hn : ¬ n ≤ 1)
    (α : Fin n → ι) (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    (v : Fin 4 → ℝ) (_hv : v ∈ (forward_light_cone : Set (Fin 4 → ℝ)))
    (C : ℝ)
    (hC : ∀ᶠ (t : ℝ) in 𝓝[>] 0, ∀ (x : Fin n → Fin 4 → ℝ),
      ‖vladimirov_H W n α
        (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ))‖ ≤ C) :
    Tendsto (fun t : ℝ => ∫ x : Fin n → Fin 4 → ℝ,
        vladimirov_H W n α
          (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ)) * f x)
      (𝓝[>] 0) (𝓝 (∫ x : Fin n → Fin 4 → ℝ,
        vladimirov_H W n α (fun i k => (x i k : ℂ)) * f x)) := by
  let bound : (Fin n → Fin 4 → ℝ) → ℝ := fun x => C * ‖f x‖
  have h_bound_integ : Integrable bound volume := f.integrable.norm.const_mul C
  have h_bound : ∀ᶠ (t : ℝ) in 𝓝[>] 0, ∀ᵐ (x : Fin n → Fin 4 → ℝ),
      ‖vladimirov_H W n α
        (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ)) * f x‖ ≤ bound x := by
    apply hC.mono
    intro t ht
    exact ae_of_all _ (fun x => by
      dsimp [bound]
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (ht x) (norm_nonneg _))
  have h_meas : ∀ᶠ (t : ℝ) in 𝓝[>] 0, AEStronglyMeasurable
      (fun x => vladimirov_H W n α
        (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ)) * f x)
      volume :=
    Filter.Eventually.of_forall
      (fun t => aestronglyMeasurable_vladimirov_H_integrand W n hn α f t v)
  have h_lim : ∀ᵐ (x : Fin n → Fin 4 → ℝ), Tendsto
      (fun t : ℝ => vladimirov_H W n α
        (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ)) * f x)
      (𝓝[>] 0)
      (𝓝 (vladimirov_H W n α (fun i k => (x i k : ℂ)) * f x)) :=
    ae_of_all _ (fun x => tendsto_vladimirov_H_mul_f_pointwise W n hn α f x v)
  exact tendsto_integral_filter_of_dominated_convergence bound h_meas h_bound h_bound_integ h_lim

omit [Fintype ι] [DecidableEq ι] in
lemma minkowskiInner_le_norm (x y : Fin 4 → ℝ) :
    |minkowskiInner x y| ≤ 4 * ‖x‖ * ‖y‖ := by
  rw [minkowskiInner_explicit]
  have h_mul : ∀ i : Fin 4, |x i * y i| ≤ ‖x‖ * ‖y‖ := by
    intro i
    rw [abs_mul]
    have hx : |x i| ≤ ‖x‖ := norm_le_pi_norm x i
    have hy : |y i| ≤ ‖y‖ := norm_le_pi_norm y i
    exact mul_le_mul hx hy (abs_nonneg _) (norm_nonneg _)
  have h0 : |x 0 * y 0 - x 1 * y 1 - x 2 * y 2 - x 3 * y 3| ≤
      |x 0 * y 0| + |x 1 * y 1| + |x 2 * y 2| + |x 3 * y 3| := by
    have h1 : |x 0 * y 0 - x 1 * y 1 - x 2 * y 2 - x 3 * y 3| =
        |(x 0 * y 0 - x 1 * y 1 - x 2 * y 2) - x 3 * y 3| := by ring_nf
    have h2 : |x 0 * y 0 - x 1 * y 1 - x 2 * y 2| =
        |(x 0 * y 0 - x 1 * y 1) - x 2 * y 2| := by ring_nf
    have ha1 := abs_sub (x 0 * y 0 - x 1 * y 1 - x 2 * y 2) (x 3 * y 3)
    have ha2 := abs_sub (x 0 * y 0 - x 1 * y 1) (x 2 * y 2)
    have ha3 := abs_sub (x 0 * y 0) (x 1 * y 1)
    linarith
  have h_sum : |x 0 * y 0| + |x 1 * y 1| + |x 2 * y 2| + |x 3 * y 3| ≤
      4 * ‖x‖ * ‖y‖ := by
    linarith [h_mul 0, h_mul 1, h_mul 2, h_mul 3]
  linarith

omit [Fintype ι] [DecidableEq ι] in
lemma sum_k_minkowskiInner_le (n : ℕ) (p : Fin n → Fin 4 → ℝ) (hp : ‖p‖ ≤ 2)
    (v : Fin 4 → ℝ) (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    t * ∑ k : Fin n, ((k : ℕ) : ℝ) * minkowskiInner (p k) v ≤
      8 * ‖v‖ * ∑ k : Fin n, ((k : ℕ) : ℝ) := by
  have ht1 : t ≤ 1 := le_of_lt ht.2
  have ht0 : 0 ≤ t := le_of_lt ht.1
  have h_term : ∀ k : Fin n, minkowskiInner (p k) v ≤ 8 * ‖v‖ := by
    intro k
    have h_abs := minkowskiInner_le_norm (p k) v
    have hpk : ‖p k‖ ≤ 2 := (norm_le_pi_norm p k).trans hp
    have h_le : minkowskiInner (p k) v ≤ |minkowskiInner (p k) v| := le_abs_self _
    have h_mul : 4 * ‖p k‖ * ‖v‖ ≤ 8 * ‖v‖ := by
      calc 4 * ‖p k‖ * ‖v‖ ≤ 4 * 2 * ‖v‖ := by gcongr
        _ = 8 * ‖v‖ := by ring
    exact h_le.trans (h_abs.trans h_mul)
  have h_sum : ∑ k : Fin n, ((k : ℕ) : ℝ) * minkowskiInner (p k) v ≤
      ∑ k : Fin n, ((k : ℕ) : ℝ) * (8 * ‖v‖) := by
    refine Finset.sum_le_sum (fun k _ => ?_)
    exact mul_le_mul_of_nonneg_left (h_term k) (Nat.cast_nonneg _)
  have h_pull : (∑ k : Fin n, ((k : ℕ) : ℝ) * (8 * ‖v‖)) =
      8 * ‖v‖ * ∑ k : Fin n, ((k : ℕ) : ℝ) := by
    rw [← Finset.sum_mul]
    ring
  rw [h_pull] at h_sum
  have h_bound_nonneg : 0 ≤ 8 * ‖v‖ * ∑ k : Fin n, ((k : ℕ) : ℝ) := by
    refine mul_nonneg (by positivity) ?_
    exact Finset.sum_nonneg (fun k _ => Nat.cast_nonneg _)
  by_cases hs : 0 ≤ ∑ k : Fin n, ((k : ℕ) : ℝ) * minkowskiInner (p k) v
  · calc t * ∑ k : Fin n, ((k : ℕ) : ℝ) * minkowskiInner (p k) v
        ≤ 1 * ∑ k : Fin n, ((k : ℕ) : ℝ) * minkowskiInner (p k) v :=
          mul_le_mul_of_nonneg_right ht1 hs
      _ = ∑ k : Fin n, ((k : ℕ) : ℝ) * minkowskiInner (p k) v := one_mul _
      _ ≤ 8 * ‖v‖ * ∑ k : Fin n, ((k : ℕ) : ℝ) := h_sum
  · push Not at hs
    have h_prod_neg : t * ∑ k : Fin n, ((k : ℕ) : ℝ) * minkowskiInner (p k) v ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos ht0 (le_of_lt hs)
    exact h_prod_neg.trans h_bound_nonneg

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_kernel_bound_inside (n : ℕ) (x : Fin n → Fin 4 → ℝ)
    (p : Fin n → Fin 4 → ℝ) (hp : ‖p‖ ≤ 2)
    (v : Fin 4 → ℝ) (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    ‖vladimirov_kernel n
        (fun i k => (x i k : ℂ) + Complex.I * ((t * ((i : ℕ) : ℝ) * v k : ℝ) : ℂ)) p‖ ≤
      Real.exp (8 * ‖v‖ * ∑ k : Fin n, ((k : ℕ) : ℝ)) := by
  rw [vladimirov_kernel_line_norm]
  exact Real.exp_le_exp.mpr (sum_k_minkowskiInner_le n p hp v t ht)

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_psi_bound_inside_zero (n : ℕ) (x : Fin n → Fin 4 → ℝ)
    (p : Fin n → Fin 4 → ℝ) (hp : ‖p‖ ≤ 2)
    (v : Fin 4 → ℝ) (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    ‖vladimirov_psi n 1 Real.zero_lt_one
        (fun i k => (x i k : ℂ) + Complex.I * ((t * ((i : ℕ) : ℝ) * v k : ℝ) : ℂ)) p‖ ≤
      Real.exp (8 * ‖v‖ * ∑ k : Fin n, ((k : ℕ) : ℝ)) := by
  dsimp [vladimirov_psi]
  rw [norm_mul]
  have h_bump : ‖((vladimirovCutoffBump n 1 Real.zero_lt_one p : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real]
    have h0 : 0 ≤ (vladimirovCutoffBump n 1 Real.zero_lt_one p : ℝ) :=
      (vladimirovCutoffBump n 1 Real.zero_lt_one).nonneg
    have h1 : (vladimirovCutoffBump n 1 Real.zero_lt_one p : ℝ) ≤ 1 :=
      (vladimirovCutoffBump n 1 Real.zero_lt_one).le_one
    rw [Real.norm_of_nonneg h0]
    exact h1
  have h_ker_bound := vladimirov_kernel_bound_inside n x p hp v t ht
  have h_ker_nonneg : 0 ≤ ‖vladimirov_kernel n
      (fun i k => (x i k : ℂ) + Complex.I * ((t * ((i : ℕ) : ℝ) * v k : ℝ) : ℂ)) p‖ :=
    norm_nonneg _
  have h_mul := mul_le_mul h_bump h_ker_bound h_ker_nonneg zero_le_one
  rw [one_mul] at h_mul
  exact h_mul

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_psi_inside_bound_zero (n : ℕ) (v : Fin 4 → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ) (_ht : t ∈ Set.Ioo (0 : ℝ) 1) (x : Fin n → Fin 4 → ℝ)
      (p : Fin n → Fin 4 → ℝ) (_hp : ‖p‖ ≤ 2),
      ‖iteratedFDeriv ℝ 0 (vladimirov_psi n 1 Real.zero_lt_one
        (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ))) p‖ ≤
        C * (1 + ‖x‖ ^ 0) := by
  use Real.exp (8 * ‖v‖ * ∑ k : Fin n, ((k : ℕ) : ℝ))
  refine ⟨by positivity, fun t ht x p hp => ?_⟩
  rw [norm_iteratedFDeriv_zero]
  have h_bound := vladimirov_psi_bound_inside_zero n x p hp v t ht
  have h_poly : (1 : ℝ) ≤ 1 + ‖x‖ ^ 0 := by
    rw [pow_zero]
    linarith
  calc ‖vladimirov_psi n 1 Real.zero_lt_one
          (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ)) p‖
      ≤ Real.exp (8 * ‖v‖ * ∑ k : Fin n, ((k : ℕ) : ℝ)) := h_bound
    _ = Real.exp (8 * ‖v‖ * ∑ k : Fin n, ((k : ℕ) : ℝ)) * 1 := by ring
    _ ≤ Real.exp (8 * ‖v‖ * ∑ k : Fin n, ((k : ℕ) : ℝ)) * (1 + ‖x‖ ^ 0) :=
        mul_le_mul_of_nonneg_left h_poly (by positivity)

lemma vladimirov_psi_norm_bound_of_spectralRegion (n : ℕ) (p : Fin n → Fin 4 → ℝ)
    (hp : p ∈ spectralRegion n) (x : Fin n → Fin 4 → ℝ)
    (v : Fin 4 → ℝ) (hv : v ∈ forward_light_cone) (t : ℝ) (ht : 0 ≤ t) :
    ‖vladimirov_psi n 1 Real.zero_lt_one
        (fun i k => (x i k : ℂ) + Complex.I * ((t * ((i : ℕ) : ℝ) * v k : ℝ) : ℂ)) p‖ ≤ 1 := by
  dsimp [vladimirov_psi]
  rw [norm_mul]
  have h_ker := vladimirov_kernel_line_norm_le_one n p hp x v hv t ht
  have h_bump : ‖((vladimirovCutoffBump n 1 Real.zero_lt_one p : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real]
    have h0 : 0 ≤ (vladimirovCutoffBump n 1 Real.zero_lt_one p : ℝ) :=
      (vladimirovCutoffBump n 1 Real.zero_lt_one).nonneg
    have h1 : (vladimirovCutoffBump n 1 Real.zero_lt_one p : ℝ) ≤ 1 :=
      (vladimirovCutoffBump n 1 Real.zero_lt_one).le_one
    rw [Real.norm_of_nonneg h0]
    exact h1
  have h_ker_nonneg : 0 ≤ ‖vladimirov_kernel n
      (fun i k => (x i k : ℂ) + Complex.I * ((t * ((i : ℕ) : ℝ) * v k : ℝ) : ℂ)) p‖ :=
    norm_nonneg _
  exact mul_le_one₀ h_bump h_ker_nonneg h_ker

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_psi_iteratedFDeriv_zero (n : ℕ) (R : ℝ) (hR : 0 < R)
    (z : Fin n → Fin 4 → ℂ) (m : ℕ)
    (p : Fin n → Fin 4 → ℝ) (hp : 2 * R < ‖p‖) :
    iteratedFDeriv ℝ m (vladimirov_psi n R hR z) p = 0 := by
  have h_eq : vladimirov_psi n R hR z =
      vladimirov_multilinear_psi n R hR z 0 Fin.elim0 := by
    ext q
    exact (vladimirov_multilinear_psi_zero n R hR z Fin.elim0 q).symm
  rw [h_eq]
  exact vladimirov_multilinear_psi_iteratedFDeriv_eq_zero n R hR z 0 Fin.elim0 m p hp

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_psi_schwartz_bound_of_inside_bound (n : ℕ) (l m : ℕ) (v : Fin 4 → ℝ)
    (C_in : ℝ) (hC_in : 0 ≤ C_in)
    (h_in : ∀ (t : ℝ) (_ht : t ∈ Set.Ioo (0 : ℝ) 1) (x : Fin n → Fin 4 → ℝ)
      (p : Fin n → Fin 4 → ℝ) (_hp : ‖p‖ ≤ 2),
      ‖iteratedFDeriv ℝ m (vladimirov_psi n 1 Real.zero_lt_one
        (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ))) p‖ ≤
        C_in * (1 + ‖x‖ ^ m)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ) (_ht : t ∈ Set.Ioo (0 : ℝ) 1) (x : Fin n → Fin 4 → ℝ),
      (schwartzSeminormFamily ℝ (Fin n → Fin 4 → ℝ) ℂ (l, m))
        (vladimirov_psi_schwartz n 1 Real.zero_lt_one
          (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ))) ≤
        C * (1 + ‖x‖ ^ m) := by
  use (2 : ℝ) ^ l * C_in
  have hC : 0 ≤ (2 : ℝ) ^ l * C_in := mul_nonneg (by positivity) hC_in
  refine ⟨hC, fun t ht x => ?_⟩
  have h_bound_nonneg : 0 ≤ ((2 : ℝ) ^ l * C_in) * (1 + ‖x‖ ^ m) :=
    mul_nonneg hC (by positivity)
  refine SchwartzMap.seminorm_le_bound ℝ l m _ h_bound_nonneg ?_
  intro p
  have h_fun_eq : ⇑(vladimirov_psi_schwartz n 1 Real.zero_lt_one
      (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ))) =
      vladimirov_psi n 1 Real.zero_lt_one
        (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ)) := rfl
  rw [h_fun_eq]
  by_cases hp : ‖p‖ ≤ 2
  · have h_pl : ‖p‖ ^ l ≤ (2 : ℝ) ^ l := pow_le_pow_left₀ (norm_nonneg _) hp l
    have h_deriv := h_in t ht x p hp
    have h_mul := mul_le_mul h_pl h_deriv (norm_nonneg _) (by positivity)
    calc ‖p‖ ^ l * ‖iteratedFDeriv ℝ m (vladimirov_psi n 1 Real.zero_lt_one
            (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ))) p‖
        ≤ (2 : ℝ) ^ l * (C_in * (1 + ‖x‖ ^ m)) := h_mul
      _ = ((2 : ℝ) ^ l * C_in) * (1 + ‖x‖ ^ m) := by ring
  · have hp_lt : 2 * 1 < ‖p‖ := by
      push Not at hp
      linarith
    have hz := vladimirov_psi_iteratedFDeriv_zero n 1 Real.zero_lt_one
      (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ)) m p hp_lt
    rw [hz, norm_zero, mul_zero]
    exact h_bound_nonneg

lemma iteratedDeriv_cexp (n : ℕ) (w : ℂ) :
    iteratedDeriv n Complex.exp w = Complex.exp w := by
  induction n generalizing w with
  | zero =>
    rfl
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have h_eq : iteratedDeriv n Complex.exp = Complex.exp := by
      ext y
      exact ih y
    rw [h_eq, Complex.deriv_exp]

lemma norm_iteratedFDeriv_complex_exp (n : ℕ) (w : ℂ) :
    ‖iteratedFDeriv ℂ n Complex.exp w‖ = Real.exp w.re := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_cexp, Complex.norm_exp]

lemma norm_iteratedFDeriv_real_exp (n : ℕ) (w : ℂ) :
    ‖iteratedFDeriv ℝ n Complex.exp w‖ = Real.exp w.re := by
  have h_cont : ContDiffAt ℂ n Complex.exp w := Complex.contDiff_exp.contDiffAt
  have h_eq := (ContDiffAt.restrictScalars_iteratedFDeriv
    (𝕜 := ℝ) (𝕜' := ℂ) (n := n) h_cont).symm
  rw [h_eq]
  rw [Function.comp_apply]
  rw [ContinuousMultilinearMap.norm_restrictScalars]
  exact norm_iteratedFDeriv_complex_exp n w

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_kernel_deriv_bound_inside (n : ℕ) (x : Fin n → Fin 4 → ℝ)
    (p : Fin n → Fin 4 → ℝ) (hp : ‖p‖ ≤ 2)
    (v : Fin 4 → ℝ) (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (vladimirov_kernel n
      (fun i k => (x i k : ℂ) + Complex.I * ((t * ((i : ℕ) : ℝ) * v k : ℝ) : ℂ))) p‖ ≤
      Real.exp (8 * ‖v‖ * ∑ k : Fin n, ((k : ℕ) : ℝ)) *
      ‖vladimirov_phase_CLM n
        (fun i k => (x i k : ℂ) + Complex.I * ((t * ((i : ℕ) : ℝ) * v k : ℝ) : ℂ))‖ ^ j := by
  let z : Fin n → Fin 4 → ℂ :=
    fun i k => (x i k : ℂ) + Complex.I * ((t * ((i : ℕ) : ℝ) * v k : ℝ) : ℂ)
  have h_comp : (vladimirov_kernel n z) = Complex.exp ∘ (vladimirov_phase_CLM n z) := rfl
  rw [h_comp]
  have h_le := norm_iteratedFDeriv_comp_clm_le
    (vladimirov_phase_CLM n z) Complex.exp Complex.contDiff_exp p j
  have h_exp_norm := norm_iteratedFDeriv_real_exp j (vladimirov_phase_CLM n z p)
  have h_norm_exp : Real.exp (vladimirov_phase_CLM n z p).re =
      ‖Complex.exp (vladimirov_phase_CLM n z p)‖ :=
    (Complex.norm_exp _).symm
  rw [h_exp_norm, h_norm_exp] at h_le
  have h_ker_eq : Complex.exp (vladimirov_phase_CLM n z p) = vladimirov_kernel n z p := rfl
  rw [h_ker_eq] at h_le
  have h_ker_bound := vladimirov_kernel_bound_inside n x p hp v t ht
  have h_pow_nonneg : 0 ≤ ‖vladimirov_phase_CLM n z‖ ^ j := by positivity
  exact h_le.trans (mul_le_mul_of_nonneg_right h_ker_bound h_pow_nonneg)

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_phase_clm_norm_le_all (n : ℕ) :
    ∃ C_L : ℝ, 0 ≤ C_L ∧ ∀ h, ‖vladimirov_phase_CLM n h‖ ≤ C_L * ‖h‖ := by
  cases n with
  | zero =>
    use 0
    refine ⟨le_rfl, fun h => ?_⟩
    have h_zero : vladimirov_phase_CLM 0 h = 0 := by
      ext p
      have hp : p = 0 := Subsingleton.elim _ 0
      subst hp
      simp only [map_zero]
    rw [h_zero, norm_zero, zero_mul]
  | succ n' =>
    exact vladimirov_phase_clm_norm_le n'

noncomputable def vladimirov_cutoff_bump_schwartz (n : ℕ) :
    SchwartzMap (Fin n → Fin 4 → ℝ) ℂ :=
  have h_supp : HasCompactSupport
      (fun p => ((vladimirovCutoffBump n 1 Real.zero_lt_one p : ℝ) : ℂ)) := by
    have h1 := (vladimirovCutoffBump n 1 Real.zero_lt_one).hasCompactSupport
    exact h1.comp_left (g := fun (r : ℝ) => (r : ℂ)) Complex.ofReal_zero
  have h_diff : ContDiff ℝ (⊤ : ℕ∞)
      (fun p => ((vladimirovCutoffBump n 1 Real.zero_lt_one p : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (vladimirovCutoffBump n 1 Real.zero_lt_one).contDiff
  h_supp.toSchwartzMap h_diff

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_cutoff_bump_deriv_bound (n : ℕ) (i : ℕ) (p : Fin n → Fin 4 → ℝ) :
    ‖iteratedFDeriv ℝ i (fun q => ((vladimirovCutoffBump n 1 Real.zero_lt_one q : ℝ) : ℂ)) p‖ ≤
      SchwartzMap.seminorm ℝ 0 i (vladimirov_cutoff_bump_schwartz n) := by
  have h_coe : (fun q => ((vladimirovCutoffBump n 1 Real.zero_lt_one q : ℝ) : ℂ)) =
      ⇑(vladimirov_cutoff_bump_schwartz n) := rfl
  rw [h_coe]
  have h := SchwartzMap.le_seminorm (𝕜 := ℝ) 0 i (vladimirov_cutoff_bump_schwartz n) p
  simp only [pow_zero, one_mul] at h
  exact h

lemma norm_minkowskiInnerC_le (p_k : Fin 4 → ℝ) (x_k : Fin 4 → ℝ) (v : Fin 4 → ℝ)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) (k : ℕ) :
    ‖minkowskiInnerC (fun μ => (p_k μ : ℂ))
      (fun μ => (x_k μ : ℂ) + Complex.I * ((t * (k : ℝ) * v μ : ℝ) : ℂ))‖ ≤
      4 * ‖p_k‖ * (‖x_k‖ + (k : ℝ) * ‖v‖) := by
  dsimp [minkowskiInnerC]
  have ht1 : |t| ≤ 1 := by
    rw [abs_le]
    exact ⟨by linarith [ht.1], le_of_lt ht.2⟩
  have h_comp : ∀ μ : Fin 4,
      ‖(p_k μ : ℂ) * ((x_k μ : ℂ) + Complex.I * ((t * (k : ℝ) * v μ : ℝ) : ℂ))‖ ≤
        ‖p_k‖ * (‖x_k‖ + (k : ℝ) * ‖v‖) := by
    intro μ
    rw [norm_mul, Complex.norm_real]
    have hp : |p_k μ| ≤ ‖p_k‖ := norm_le_pi_norm p_k μ
    have hz : ‖(x_k μ : ℂ) + Complex.I * ((t * (k : ℝ) * v μ : ℝ) : ℂ)‖ ≤
        ‖x_k‖ + (k : ℝ) * ‖v‖ := by
      refine (norm_add_le _ _).trans ?_
      rw [Complex.norm_real, norm_mul, Complex.norm_I, one_mul, Complex.norm_real]
      rw [Real.norm_eq_abs, Real.norm_eq_abs]
      have hx : |x_k μ| ≤ ‖x_k‖ := norm_le_pi_norm x_k μ
      have hv : |v μ| ≤ ‖v‖ := norm_le_pi_norm v μ
      have hk_nonneg : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      have h_abs_tkv : |t * (k : ℝ) * v μ| ≤ (k : ℝ) * ‖v‖ := by
        calc |t * (k : ℝ) * v μ|
            = |t| * (k : ℝ) * |v μ| := by
              rw [abs_mul, abs_mul, abs_of_nonneg hk_nonneg]
          _ ≤ 1 * (k : ℝ) * ‖v‖ := by
              refine mul_le_mul (mul_le_mul_of_nonneg_right ht1 hk_nonneg)
                hv (abs_nonneg _) (mul_nonneg zero_le_one hk_nonneg)
          _ = (k : ℝ) * ‖v‖ := by ring
      linarith
    exact mul_le_mul hp hz (norm_nonneg _) (norm_nonneg _)
  have h_sub4 : ∀ (a b c d : ℂ), ‖a - b - c - d‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by
    intro a b c d
    calc ‖a - b - c - d‖
        ≤ ‖a - b - c‖ + ‖d‖ := norm_sub_le _ _
      _ ≤ ‖a - b‖ + ‖c‖ + ‖d‖ := by linarith [norm_sub_le (a - b) c]
      _ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ := by linarith [norm_sub_le a b]
  have h4 := h_sub4
    ((p_k 0 : ℂ) * ((x_k 0 : ℂ) + Complex.I * ((t * (k : ℝ) * v 0 : ℝ) : ℂ)))
    ((p_k 1 : ℂ) * ((x_k 1 : ℂ) + Complex.I * ((t * (k : ℝ) * v 1 : ℝ) : ℂ)))
    ((p_k 2 : ℂ) * ((x_k 2 : ℂ) + Complex.I * ((t * (k : ℝ) * v 2 : ℝ) : ℂ)))
    ((p_k 3 : ℂ) * ((x_k 3 : ℂ) + Complex.I * ((t * (k : ℝ) * v 3 : ℝ) : ℂ)))
  have h0 := h_comp 0
  have h1 := h_comp 1
  have h2 := h_comp 2
  have h3 := h_comp 3
  linarith

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_phase_clm_opnorm_le (n : ℕ) (x : Fin n → Fin 4 → ℝ) (v : Fin 4 → ℝ)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    ‖vladimirov_phase_CLM n
      (fun i k => (x i k : ℂ) + Complex.I * ((t * ((i : ℕ) : ℝ) * v k : ℝ) : ℂ))‖ ≤
      4 * ((n : ℝ) * ‖x‖ + ‖v‖ * ∑ k : Fin n, ((k : ℕ) : ℝ)) := by
  let z : Fin n → Fin 4 → ℂ :=
    fun i k => (x i k : ℂ) + Complex.I * ((t * ((i : ℕ) : ℝ) * v k : ℝ) : ℂ)
  have h_bound_nonneg : 0 ≤ 4 * ((n : ℝ) * ‖x‖ + ‖v‖ * ∑ k : Fin n, ((k : ℕ) : ℝ)) := by
    positivity
  refine ContinuousLinearMap.opNorm_le_bound _ h_bound_nonneg (fun p => ?_)
  rw [vladimirov_phase_clm_eq_phase_z_clm]
  dsimp [vladimirov_phase_z_CLM, LinearMap.toContinuousLinearMap, vladimirov_phase_z_LM]
  rw [norm_mul, norm_neg, Complex.norm_I, one_mul]
  refine (norm_sum_le _ _).trans ?_
  have h_term : ∀ k : Fin n,
      ‖minkowskiInnerC (fun μ => (p k μ : ℂ)) (z k)‖ ≤
        4 * ‖p‖ * (‖x‖ + ((k : ℕ) : ℝ) * ‖v‖) := by
    intro k
    have h_le := norm_minkowskiInnerC_le (p k) (x k) v t ht (k : ℕ)
    have hpk : ‖p k‖ ≤ ‖p‖ := norm_le_pi_norm p k
    have hxk : ‖x k‖ ≤ ‖x‖ := norm_le_pi_norm x k
    have h_mul1 : ‖p k‖ * (‖x k‖ + ((k : ℕ) : ℝ) * ‖v‖) ≤
        ‖p‖ * (‖x‖ + ((k : ℕ) : ℝ) * ‖v‖) := by
      have h1 : ‖x k‖ + ((k : ℕ) : ℝ) * ‖v‖ ≤ ‖x‖ + ((k : ℕ) : ℝ) * ‖v‖ := by linarith
      have h2 : 0 ≤ ‖x k‖ + ((k : ℕ) : ℝ) * ‖v‖ := by positivity
      exact mul_le_mul hpk h1 h2 (norm_nonneg _)
    calc ‖minkowskiInnerC (fun μ => (p k μ : ℂ)) (z k)‖
        ≤ 4 * ‖p k‖ * (‖x k‖ + ((k : ℕ) : ℝ) * ‖v‖) := h_le
      _ = 4 * (‖p k‖ * (‖x k‖ + ((k : ℕ) : ℝ) * ‖v‖)) := by ring
      _ ≤ 4 * (‖p‖ * (‖x‖ + ((k : ℕ) : ℝ) * ‖v‖)) := by linarith
      _ = 4 * ‖p‖ * (‖x‖ + ((k : ℕ) : ℝ) * ‖v‖) := by ring
  have h_sum : (∑ k : Fin n, ‖minkowskiInnerC (fun μ => (p k μ : ℂ)) (z k)‖) ≤
      ∑ k : Fin n, (4 * ‖p‖ * (‖x‖ + ((k : ℕ) : ℝ) * ‖v‖)) :=
    Finset.sum_le_sum (fun k _ => h_term k)
  refine h_sum.trans ?_
  have h_ring : (∑ k : Fin n, (4 * ‖p‖ * (‖x‖ + ((k : ℕ) : ℝ) * ‖v‖))) =
      4 * ((n : ℝ) * ‖x‖ + ‖v‖ * ∑ k : Fin n, ((k : ℕ) : ℝ)) * ‖p‖ := by
    rw [← Finset.mul_sum]
    have h_split : (∑ k : Fin n, (‖x‖ + ((k : ℕ) : ℝ) * ‖v‖)) =
        (n : ℝ) * ‖x‖ + ‖v‖ * ∑ k : Fin n, ((k : ℕ) : ℝ) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
      congr 1
      · simp only [Finset.card_univ, Fintype.card_fin]
      · simp_rw [mul_comm _ ‖v‖]
        rw [← Finset.mul_sum]
    rw [h_split]
    ring
  rw [h_ring]

lemma pow_one_add_le_two_pow_mul (r : ℝ) (hr : 0 ≤ r) (j m : ℕ) (hjm : j ≤ m) :
    (1 + r) ^ j ≤ 2 ^ m * (1 + r ^ m) := by
  by_cases h : r ≤ 1
  · have h1 : 1 + r ≤ 2 := by linarith
    have h2 : (1 + r) ^ j ≤ 2 ^ j := by
      refine pow_le_pow_left₀ (by linarith) h1 j
    have h3 : (2 : ℝ) ^ j ≤ 2 ^ m := by
      refine pow_le_pow_right₀ (by norm_num) hjm
    have h5 : (2 : ℝ) ^ m ≤ 2 ^ m * (1 + r ^ m) := by
      have hrm : 0 ≤ r ^ m := by positivity
      have h_one : (1 : ℝ) ≤ 1 + r ^ m := by linarith
      have hmul := mul_le_mul_of_nonneg_left h_one (by positivity : 0 ≤ (2 : ℝ) ^ m)
      linarith
    linarith
  · push Not at h
    have h1 : 1 + r ≤ 2 * r := by linarith
    have h2 : (1 + r) ^ j ≤ (2 * r) ^ j := by
      refine pow_le_pow_left₀ (by linarith) h1 j
    rw [mul_pow] at h2
    have h3 : (2 : ℝ) ^ j ≤ 2 ^ m := by
      refine pow_le_pow_right₀ (by norm_num) hjm
    have h4 : r ^ j ≤ r ^ m := by
      refine pow_le_pow_right₀ h.le hjm
    have h5 : (2 : ℝ) ^ j * r ^ j ≤ 2 ^ m * r ^ m := by
      refine mul_le_mul h3 h4 (by positivity) (by positivity)
    have h6 : 2 ^ m * r ^ m ≤ 2 ^ m * (1 + r ^ m) := by
      have : r ^ m ≤ 1 + r ^ m := by linarith
      exact mul_le_mul_of_nonneg_left this (by positivity)
    linarith

lemma opnorm_phase_le_D_mul_one_add_norm (n : ℕ) (x : Fin n → Fin 4 → ℝ) (v : Fin 4 → ℝ) :
    4 * ((n : ℝ) * ‖x‖ + ‖v‖ * ∑ k : Fin n, ((k : ℕ) : ℝ)) ≤
      4 * ((n : ℝ) + ‖v‖ * ∑ k : Fin n, ((k : ℕ) : ℝ)) * (1 + ‖x‖) := by
  have h_eq : 4 * ((n : ℝ) + ‖v‖ * ∑ k : Fin n, ((k : ℕ) : ℝ)) * (1 + ‖x‖) -
      4 * ((n : ℝ) * ‖x‖ + ‖v‖ * ∑ k : Fin n, ((k : ℕ) : ℝ)) =
      4 * (n : ℝ) + 4 * (‖v‖ * ∑ k : Fin n, ((k : ℕ) : ℝ)) * ‖x‖ := by ring
  have h_pos : 0 ≤ 4 * (n : ℝ) + 4 * (‖v‖ * ∑ k : Fin n, ((k : ℕ) : ℝ)) * ‖x‖ := by
    positivity
  linarith

lemma vladimirov_psi_inside_poly_bound (n : ℕ) (m : ℕ) (v : Fin 4 → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ) (_ht : t ∈ Set.Ioo (0 : ℝ) 1) (x : Fin n → Fin 4 → ℝ)
      (p : Fin n → Fin 4 → ℝ) (_hp : ‖p‖ ≤ 2),
      ‖iteratedFDeriv ℝ m (vladimirov_psi n 1 Real.zero_lt_one
        (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ))) p‖ ≤
        C * (1 + ‖x‖ ^ m) := by
  let D : ℝ := 4 * ((n : ℝ) + ‖v‖ * ∑ k : Fin n, ((k : ℕ) : ℝ))
  let C : ℝ := ∑ i ∈ Finset.range (m + 1),
    ((m.choose i : ℝ) *
     SchwartzMap.seminorm ℝ 0 i (vladimirov_cutoff_bump_schwartz n) *
     (Real.exp (8 * ‖v‖ * ∑ k : Fin n, ((k : ℕ) : ℝ)) *
      D ^ (m - i) * (2 : ℝ) ^ m))
  have hC : 0 ≤ C := by
    refine Finset.sum_nonneg fun i _ => ?_
    positivity
  use C, hC
  intro t ht x p hp
  let z : Fin n → Fin 4 → ℂ :=
    fun i k => (x i k : ℂ) + Complex.I * ((t * ((i : ℕ) : ℝ) * v k : ℝ) : ℂ)
  let f : (Fin n → Fin 4 → ℝ) → ℂ :=
    fun q => ((vladimirovCutoffBump n 1 Real.zero_lt_one q : ℝ) : ℂ)
  let g : (Fin n → Fin 4 → ℝ) → ℂ := vladimirov_kernel n z
  have hf : ContDiff ℝ (⊤ : ℕ∞) f :=
    Complex.ofRealCLM.contDiff.comp (vladimirovCutoffBump n 1 Real.zero_lt_one).contDiff
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := vladimirov_kernel_contDiff n z
  have h_le := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (E := Fin n → Fin 4 → ℝ) (A := ℂ)
    (f := f) (g := g) (n := m) (N := (⊤ : ℕ∞))
    hf hg p (WithTop.coe_le_coe.mpr le_top)
  have h_psi_eq : (fun q => f q * g q) = vladimirov_psi n 1 Real.zero_lt_one z := rfl
  rw [h_psi_eq] at h_le
  refine h_le.trans ?_
  have h_term_le : ∀ i ∈ Finset.range (m + 1),
      ((m.choose i : ℝ) * ‖iteratedFDeriv ℝ i f p‖ * ‖iteratedFDeriv ℝ (m - i) g p‖) ≤
        ((m.choose i : ℝ) *
         SchwartzMap.seminorm ℝ 0 i (vladimirov_cutoff_bump_schwartz n) *
         (Real.exp (8 * ‖v‖ * ∑ k : Fin n, ((k : ℕ) : ℝ)) *
          D ^ (m - i) * (2 : ℝ) ^ m)) * (1 + ‖x‖ ^ m) := by
    intro i hi
    have h_sub_le : m - i ≤ m := Nat.sub_le m i
    have hf_i := vladimirov_cutoff_bump_deriv_bound n i p
    have hg_i := vladimirov_kernel_deriv_bound_inside n x p hp v t ht (m - i)
    have h_opnorm := vladimirov_phase_clm_opnorm_le n x v t ht
    have h_opnorm_D := opnorm_phase_le_D_mul_one_add_norm n x v
    have h_opnorm_le : ‖vladimirov_phase_CLM n z‖ ≤ D * (1 + ‖x‖) :=
      h_opnorm.trans h_opnorm_D
    have h_pow_le : ‖vladimirov_phase_CLM n z‖ ^ (m - i) ≤ (D * (1 + ‖x‖)) ^ (m - i) := by
      refine pow_le_pow_left₀ (norm_nonneg _) h_opnorm_le (m - i)
    rw [mul_pow] at h_pow_le
    have h_one_add := pow_one_add_le_two_pow_mul ‖x‖ (norm_nonneg _) (m - i) m h_sub_le
    have h_pow_full : ‖vladimirov_phase_CLM n z‖ ^ (m - i) ≤
        D ^ (m - i) * ((2 : ℝ) ^ m * (1 + ‖x‖ ^ m)) := by
      refine h_pow_le.trans ?_
      exact mul_le_mul_of_nonneg_left h_one_add (by positivity)
    have h_pow_full' : ‖vladimirov_phase_CLM n z‖ ^ (m - i) ≤
        (D ^ (m - i) * (2 : ℝ) ^ m) * (1 + ‖x‖ ^ m) := by
      calc ‖vladimirov_phase_CLM n z‖ ^ (m - i)
          ≤ D ^ (m - i) * ((2 : ℝ) ^ m * (1 + ‖x‖ ^ m)) := h_pow_full
        _ = (D ^ (m - i) * (2 : ℝ) ^ m) * (1 + ‖x‖ ^ m) := by ring
    have hg_bound : ‖iteratedFDeriv ℝ (m - i) g p‖ ≤
        (Real.exp (8 * ‖v‖ * ∑ k : Fin n, ((k : ℕ) : ℝ)) *
          D ^ (m - i) * (2 : ℝ) ^ m) * (1 + ‖x‖ ^ m) := by
      calc ‖iteratedFDeriv ℝ (m - i) g p‖
          ≤ Real.exp (8 * ‖v‖ * ∑ k : Fin n, ((k : ℕ) : ℝ)) *
              ‖vladimirov_phase_CLM n z‖ ^ (m - i) := hg_i
        _ ≤ Real.exp (8 * ‖v‖ * ∑ k : Fin n, ((k : ℕ) : ℝ)) *
              ((D ^ (m - i) * (2 : ℝ) ^ m) * (1 + ‖x‖ ^ m)) := by
            refine mul_le_mul_of_nonneg_left h_pow_full' (by positivity)
        _ = (Real.exp (8 * ‖v‖ * ∑ k : Fin n, ((k : ℕ) : ℝ)) *
              D ^ (m - i) * (2 : ℝ) ^ m) * (1 + ‖x‖ ^ m) := by ring
    have h_step1 : (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i f p‖ ≤
        (m.choose i : ℝ) * SchwartzMap.seminorm ℝ 0 i (vladimirov_cutoff_bump_schwartz n) :=
      mul_le_mul_of_nonneg_left hf_i (Nat.cast_nonneg _)
    have h_step2 : ((m.choose i : ℝ) * ‖iteratedFDeriv ℝ i f p‖) * ‖iteratedFDeriv ℝ (m - i) g p‖ ≤
        ((m.choose i : ℝ) * SchwartzMap.seminorm ℝ 0 i (vladimirov_cutoff_bump_schwartz n)) *
          ((Real.exp (8 * ‖v‖ * ∑ k : Fin n, ((k : ℕ) : ℝ)) *
            D ^ (m - i) * (2 : ℝ) ^ m) * (1 + ‖x‖ ^ m)) := by
      refine mul_le_mul h_step1 hg_bound (norm_nonneg _) (by positivity)
    calc ((m.choose i : ℝ) * ‖iteratedFDeriv ℝ i f p‖ * ‖iteratedFDeriv ℝ (m - i) g p‖)
        = ((m.choose i : ℝ) * ‖iteratedFDeriv ℝ i f p‖) * ‖iteratedFDeriv ℝ (m - i) g p‖ := by ring
      _ ≤ ((m.choose i : ℝ) * SchwartzMap.seminorm ℝ 0 i (vladimirov_cutoff_bump_schwartz n)) *
            ((Real.exp (8 * ‖v‖ * ∑ k : Fin n, ((k : ℕ) : ℝ)) *
              D ^ (m - i) * (2 : ℝ) ^ m) * (1 + ‖x‖ ^ m)) := h_step2
      _ = ((m.choose i : ℝ) *
           SchwartzMap.seminorm ℝ 0 i (vladimirov_cutoff_bump_schwartz n) *
           (Real.exp (8 * ‖v‖ * ∑ k : Fin n, ((k : ℕ) : ℝ)) *
            D ^ (m - i) * (2 : ℝ) ^ m)) * (1 + ‖x‖ ^ m) := by ring
  have h_sum_le := Finset.sum_le_sum h_term_le
  refine h_sum_le.trans ?_
  rw [← Finset.sum_mul]

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_psi_schwartz_seminorm_poly_bound (n : ℕ) (l m : ℕ)
    (v : Fin 4 → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ) (_ht : t ∈ Set.Ioo (0 : ℝ) 1) (x : Fin n → Fin 4 → ℝ),
      (schwartzSeminormFamily ℝ (Fin n → Fin 4 → ℝ) ℂ (l, m))
        (vladimirov_psi_schwartz n 1 Real.zero_lt_one
          (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ))) ≤
        C * (1 + ‖x‖ ^ m) := by
  obtain ⟨C_in, hC_in, h_in⟩ := vladimirov_psi_inside_poly_bound n m v
  exact vladimirov_psi_schwartz_bound_of_inside_bound n l m v C_in hC_in h_in

lemma one_add_pow_le_two_mul_one_add_pow (r : ℝ) (hr : 0 ≤ r) (a b : ℕ) (hab : a ≤ b) :
    1 + r ^ a ≤ 2 * (1 + r ^ b) := by
  by_cases h : r ≤ 1
  · have hra : r ^ a ≤ 1 := by
      cases a with
      | zero => simp
      | succ a' => exact pow_le_one₀ hr h
    have hrb : 0 ≤ r ^ b := by positivity
    linarith
  · push Not at h
    have h_le : r ^ a ≤ r ^ b := pow_le_pow_right₀ h.le hab
    have hrb : 0 ≤ r ^ b := by positivity
    linarith

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_psi_schwartz_finset_poly_bound (n : ℕ) (s : Finset (ℕ × ℕ))
    (v : Fin 4 → ℝ)
    (h_single : ∀ lm ∈ s, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (t : ℝ) (_ht : t ∈ Set.Ioo (0 : ℝ) 1) (x : Fin n → Fin 4 → ℝ),
        (schwartzSeminormFamily ℝ (Fin n → Fin 4 → ℝ) ℂ lm)
          (vladimirov_psi_schwartz n 1 Real.zero_lt_one
            (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ))) ≤
          C * (1 + ‖x‖ ^ lm.2)) :
    ∃ C : ℝ, ∃ m : ℕ, 0 ≤ C ∧
      ∀ (t : ℝ) (_ht : t ∈ Set.Ioo (0 : ℝ) 1) (x : Fin n → Fin 4 → ℝ),
        (s.sup (schwartzSeminormFamily ℝ (Fin n → Fin 4 → ℝ) ℂ))
          (vladimirov_psi_schwartz n 1 Real.zero_lt_one
            (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ))) ≤
          C * (1 + ‖x‖ ^ m) := by
  induction s using Finset.induction_on with
  | empty =>
    use 0, 0
    refine ⟨le_rfl, ?_⟩
    intro t _ht x
    rw [Finset.sup_empty]
    change 0 ≤ (0 : ℝ) * (1 + ‖x‖ ^ 0)
    simp
  | @insert a s' ha ih =>
    have h_single_a := h_single a (Finset.mem_insert_self a s')
    have h_single_s : ∀ lm ∈ s', _ := fun lm hlm => h_single lm (Finset.mem_insert_of_mem hlm)
    obtain ⟨Ca, hCa_nonneg, h_a⟩ := h_single_a
    obtain ⟨Cs, Ms, hCs_nonneg, h_s⟩ := ih h_single_s
    let C := 2 * max Ca Cs
    let M := max a.2 Ms
    have hC_nonneg : 0 ≤ C := mul_nonneg (by norm_num) (le_max_of_le_left hCa_nonneg)
    use C, M
    refine ⟨hC_nonneg, ?_⟩
    intro t ht x
    rw [Finset.sup_insert, Seminorm.sup_apply]
    have h_ha := h_a t ht x
    have h_hs := h_s t ht x
    have ha_bound := one_add_pow_le_two_mul_one_add_pow ‖x‖ (norm_nonneg _)
      a.2 M (le_max_left a.2 Ms)
    have hs_bound := one_add_pow_le_two_mul_one_add_pow ‖x‖ (norm_nonneg _)
      Ms M (le_max_right a.2 Ms)
    have ha_le : Ca * (1 + ‖x‖ ^ a.2) ≤ C * (1 + ‖x‖ ^ M) := by
      calc Ca * (1 + ‖x‖ ^ a.2)
          ≤ (max Ca Cs) * (2 * (1 + ‖x‖ ^ M)) :=
            mul_le_mul (le_max_left Ca Cs) ha_bound (by positivity) (le_max_of_le_left hCa_nonneg)
        _ = C * (1 + ‖x‖ ^ M) := by ring
    have hs_le : Cs * (1 + ‖x‖ ^ Ms) ≤ C * (1 + ‖x‖ ^ M) := by
      calc Cs * (1 + ‖x‖ ^ Ms)
          ≤ (max Ca Cs) * (2 * (1 + ‖x‖ ^ M)) :=
            mul_le_mul (le_max_right Ca Cs) hs_bound (by positivity) (le_max_of_le_left hCa_nonneg)
        _ = C * (1 + ‖x‖ ^ M) := by ring
    exact max_le (h_ha.trans ha_le) (h_hs.trans hs_le)

lemma vladimirov_H_poly_bounded (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (_hP : PoincareCovariant R W) (n : ℕ) (_hn : ¬ n ≤ 1)
    (α : Fin n → ι) (v : Fin 4 → ℝ) (_hv : v ∈ forward_light_cone) :
    ∃ C : ℝ, ∃ m : ℕ, ∀ᶠ (t : ℝ) in 𝓝[>] 0, ∀ (x : Fin n → Fin 4 → ℝ),
      ‖vladimirov_H W n α
        (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ))‖ ≤
        C * (1 + ‖x‖ ^ m) := by
  let T : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ →L[ℂ] ℂ :=
    (W n α).comp (invMinkowskiFourierCLM n)
  obtain ⟨s, CT, hCT_pos, hT_bound⟩ := schwartz_clm_bound n T
  have h_bound_each : ∀ lm ∈ s, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (t : ℝ) (_ht : t ∈ Set.Ioo (0 : ℝ) 1) (x : Fin n → Fin 4 → ℝ),
        (schwartzSeminormFamily ℝ (Fin n → Fin 4 → ℝ) ℂ lm)
          (vladimirov_psi_schwartz n 1 Real.zero_lt_one
            (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ))) ≤
          C * (1 + ‖x‖ ^ lm.2) := by
    intro lm _
    exact vladimirov_psi_schwartz_seminorm_poly_bound n lm.1 lm.2 v
  obtain ⟨Cs, M, hCs_nonneg, h_sup_le⟩ :=
    vladimirov_psi_schwartz_finset_poly_bound n s v h_bound_each
  use CT * Cs, M
  have h_eventually : ∀ᶠ (t : ℝ) in 𝓝[>] 0, t ∈ Set.Ioo (0 : ℝ) 1 := by
    have h_lt : ∀ᶠ (t : ℝ) in 𝓝[>] 0, t < 1 :=
      nhdsWithin_le_nhds (Iio_mem_nhds Real.zero_lt_one)
    have h_gt : ∀ᶠ (t : ℝ) in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
    exact h_gt.and h_lt
  refine h_eventually.mono fun t ht x => ?_
  have ht_ioo : t ∈ Set.Ioo (0 : ℝ) 1 := ht
  have hT := hT_bound (vladimirov_psi_schwartz n 1 Real.zero_lt_one
    (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ)))
  have h_sup := h_sup_le t ht_ioo x
  calc ‖vladimirov_H W n α (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ))‖
      = ‖T (vladimirov_psi_schwartz n 1 Real.zero_lt_one
          (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ)))‖ := rfl
    _ ≤ CT * (s.sup (schwartzSeminormFamily ℝ (Fin n → Fin 4 → ℝ) ℂ))
          (vladimirov_psi_schwartz n 1 Real.zero_lt_one
            (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ))) := hT
    _ ≤ CT * (Cs * (1 + ‖x‖ ^ M)) := by gcongr
    _ = (CT * Cs) * (1 + ‖x‖ ^ M) := by ring

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_H_real_def (W : WightmanFamily ι) (n : ℕ) (α : Fin n → ι)
    (x : Fin n → Fin 4 → ℝ) :
    vladimirov_H W n α (fun i k => (x i k : ℂ)) =
      W n α (invMinkowskiFourierCLM n (vladimirov_psi_schwartz n 1 Real.zero_lt_one
        (fun i k => (x i k : ℂ)))) := by
  rfl

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_psi_real_zero_of_two_le (n : ℕ) (z : Fin n → Fin 4 → ℂ)
    (p : Fin n → Fin 4 → ℝ) (hp : 2 ≤ ‖p‖) :
    vladimirov_psi n 1 Real.zero_lt_one z p = 0 := by
  dsimp [vladimirov_psi]
  have hb := vladimirovCutoffBump_eq_zero_of_two_le n p hp
  rw [hb, Complex.ofReal_zero, MulZeroClass.zero_mul]

omit [Fintype ι] [DecidableEq ι] in
lemma integral_f_mul_psi_real_zero_of_two_le (n : ℕ) (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    (p : Fin n → Fin 4 → ℝ) (hp : 2 ≤ ‖p‖) :
    (∫ x : Fin n → Fin 4 → ℝ, f x * vladimirov_psi n 1 Real.zero_lt_one
        (fun i k => (x i k : ℂ)) p) = 0 := by
  have h_zero : ∀ x, f x * vladimirov_psi n 1 Real.zero_lt_one (fun i k => (x i k : ℂ)) p = 0 := by
    intro x
    rw [vladimirov_psi_real_zero_of_two_le n (fun i k => (x i k : ℂ)) p hp, mul_zero]
  simp_rw [h_zero, integral_zero]

omit [Fintype ι] [DecidableEq ι] in
lemma integral_f_mul_psi_real_hasCompactSupport (n : ℕ) (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    HasCompactSupport (fun p : Fin n → Fin 4 → ℝ =>
      ∫ x : Fin n → Fin 4 → ℝ, f x * vladimirov_psi n 1 Real.zero_lt_one
        (fun i k => (x i k : ℂ)) p) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall 0 2)
  intro p hp
  rw [Function.mem_support] at hp
  by_contra h_not
  rw [Metric.mem_closedBall, dist_zero_right] at h_not
  push Not at h_not
  have hz := integral_f_mul_psi_real_zero_of_two_le n f p (le_of_lt h_not)
  exact hp hz

omit [Fintype ι] [DecidableEq ι] in
lemma integral_f_mul_psi_real_eq_cutoff_mul_fourier (n : ℕ)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) (p : Fin n → Fin 4 → ℝ) :
    (∫ x : Fin n → Fin 4 → ℝ, f x * vladimirov_psi n 1 Real.zero_lt_one
        (fun i k => (x i k : ℂ)) p) =
    ((vladimirovCutoffBump n 1 Real.zero_lt_one p : ℝ) : ℂ) * minkowskiFourier f p := by
  have hv : (0 : Fin 4 → ℝ) ∈ forward_light_cone ∨ True := Or.inr trivial
  have h1 := (vladimirov_boundary_F_zero_eq_integral n f 0 p).symm
  have h2 := vladimirov_boundary_F_zero n 1 Real.zero_lt_one f 0 p
  rw [h1, h2]

omit [Fintype ι] [DecidableEq ι] in
lemma cutoff_mul_fourier_hasCompactSupport (n : ℕ)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    HasCompactSupport (fun p : Fin n → Fin 4 → ℝ =>
      ((vladimirovCutoffBump n 1 Real.zero_lt_one p : ℝ) : ℂ) * minkowskiFourier f p) := by
  have h_eq : (fun p : Fin n → Fin 4 → ℝ =>
      ((vladimirovCutoffBump n 1 Real.zero_lt_one p : ℝ) : ℂ) * minkowskiFourier f p) =
    (fun p => ∫ x : Fin n → Fin 4 → ℝ, f x * vladimirov_psi n 1 Real.zero_lt_one
        (fun i k => (x i k : ℂ)) p) := by
    ext p
    exact (integral_f_mul_psi_real_eq_cutoff_mul_fourier n f p).symm
  rw [h_eq]
  exact integral_f_mul_psi_real_hasCompactSupport n f

omit [Fintype ι] [DecidableEq ι] in
lemma cutoff_mul_fourier_sub_zero_on_ball (n : ℕ)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    (p : Fin n → Fin 4 → ℝ) (hp : p ∈ Metric.ball (0 : Fin n → Fin 4 → ℝ) 1) :
    ((vladimirovCutoffBump n 1 Real.zero_lt_one p : ℝ) : ℂ) * minkowskiFourier f p -
    minkowskiFourier f p = 0 := by
  rw [vladimirov_cutoff_mul_fourier_eq_on_ball n f p hp, sub_self]

omit [Fintype ι] [DecidableEq ι] in
lemma fourier_diff_zero_of_cutoff_fourier_eq (n : ℕ)
    (f g : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    (p : Fin n → Fin 4 → ℝ)
    (hfg : minkowskiFourier g p =
      ((vladimirovCutoffBump n 1 Real.zero_lt_one p : ℝ) : ℂ) * minkowskiFourier f p)
    (hp : p ∈ Metric.ball (0 : Fin n → Fin 4 → ℝ) 1) :
    minkowskiFourier (g - f) p = 0 := by
  rw [minkowskiFourier_sub, hfg]
  exact cutoff_mul_fourier_sub_zero_on_ball n f p hp

omit [Fintype ι] [DecidableEq ι] in
lemma W_eq_of_scaledCom_fourier_diff_zero (W : WightmanFamily ι)
    (hspec : SpectrumCondition W) (n : ℕ) (α : Fin n → ι)
    (f g : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    (hfg : ∀ p ∈ scaledComNeighborhood n 1 1, minkowskiFourier (g - f) p = 0) :
    W n α g = W n α f := by
  have h_sub := close_lorentz_cov_step W hspec n 1 α g f hfg
  exact sub_eq_zero.mp h_sub

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_H_real_eq_of_comm (W : WightmanFamily ι)
    (hspec : SpectrumCondition W) (n : ℕ)
    (α : Fin n → ι) (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    (g : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    (hfg : ∀ p ∈ scaledComNeighborhood n 1 1, minkowskiFourier (g - f) p = 0)
    (h_comm : (∫ x : Fin n → Fin 4 → ℝ, vladimirov_H W n α (fun i k => (x i k : ℂ)) * f x) =
      W n α g) :
    (∫ x : Fin n → Fin 4 → ℝ, vladimirov_H W n α (fun i k => (x i k : ℂ)) * f x) = W n α f := by
  rw [h_comm]
  exact W_eq_of_scaledCom_fourier_diff_zero W hspec n α f g hfg

lemma vladimirov_H_real_eq_le_one (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (hspec : SpectrumCondition W) (hP : PoincareCovariant R W) (n : ℕ) (hn : n ≤ 1)
    (α : Fin n → ι) (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    (∫ x : Fin n → Fin 4 → ℝ, vladimirov_H W n α (fun i k => (x i k : ℂ)) * f x) = W n α f := by
  interval_cases n
  · have hW := W_zero_eq_integral W α f
    rw [hW]
    have hH : ∀ x : Fin 0 → Fin 4 → ℝ,
        vladimirov_H W 0 α (fun i k => (x i k : ℂ)) = vladimirov_H W 0 α 0 := by
      intro x
      have hx0 : x = 0 := Subsingleton.elim x 0
      subst hx0
      rfl
    simp_rw [hH]
    rw [integral_const_mul]
  · have hW := W_one_eq_integral R W hspec hP α f
    have hH := vladimirov_H_boundary_integrand_eq R W hP α f 0 0
    simp only [MulZeroClass.zero_mul, Complex.ofReal_zero, mul_zero, add_zero] at hH
    rw [hW, hH]

def unit_time_vector : Fin 4 → ℝ := fun i => if i = 0 then 1 else 0

lemma unit_time_vector_mem_forward_light_cone :
    unit_time_vector ∈ forward_light_cone := by
  constructor
  · simp [unit_time_vector]
  · simp [minkowskiInner_explicit, unit_time_vector]

lemma exists_mem_forward_light_cone : ∃ v : Fin 4 → ℝ, v ∈ forward_light_cone :=
  ⟨unit_time_vector, unit_time_vector_mem_forward_light_cone⟩

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_H_real_eq_of_tendsto_unique
    (W : WightmanFamily ι) (n : ℕ) (α : Fin n → ι)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    (v : Fin 4 → ℝ)
    (h_tend_real : Tendsto (fun t : ℝ => ∫ x : Fin n → Fin 4 → ℝ,
        vladimirov_H W n α
          (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ)) * f x)
      (𝓝[>] 0) (𝓝 (∫ x : Fin n → Fin 4 → ℝ,
        vladimirov_H W n α (fun i k => (x i k : ℂ)) * f x)))
    (h_tend_W : Tendsto (fun t : ℝ => ∫ x : Fin n → Fin 4 → ℝ,
        vladimirov_H W n α
          (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ)) * f x)
      (𝓝[>] 0) (𝓝 (W n α f))) :
    (∫ x : Fin n → Fin 4 → ℝ, vladimirov_H W n α (fun i k => (x i k : ℂ)) * f x) = W n α f :=
  tendsto_nhds_unique h_tend_real h_tend_W

lemma vladimirov_H_tend_real (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (hP : PoincareCovariant R W) (n : ℕ) (hn : ¬ n ≤ 1) (α : Fin n → ι)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    (v : Fin 4 → ℝ) (hv : v ∈ forward_light_cone) :
    Tendsto (fun t : ℝ => ∫ x : Fin n → Fin 4 → ℝ,
        vladimirov_H W n α
          (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ)) * f x)
      (𝓝[>] 0) (𝓝 (∫ x : Fin n → Fin 4 → ℝ,
        vladimirov_H W n α (fun i k => (x i k : ℂ)) * f x)) := by
  obtain ⟨C, m, hC⟩ := vladimirov_H_poly_bounded R W hP n hn α v hv
  exact vladimirov_H_boundary_step_h_tend_real_of_poly W n hn α f v hv C m hC

lemma vladimirov_kernel_zero_p_n (n : ℕ) (z : Fin n → Fin 4 → ℂ) :
    vladimirov_kernel n z 0 = 1 := by
  dsimp [vladimirov_kernel]
  have h_zero : (∑ k : Fin n, minkowskiInnerC (fun _ => 0) (z k)) = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    dsimp [minkowskiInnerC]
    ring
  rw [h_zero]
  ring_nf
  exact Complex.exp_zero

lemma vladimirov_psi_zero_p_n (n : ℕ) (z : Fin n → Fin 4 → ℂ) :
    vladimirov_psi n 1 Real.zero_lt_one z 0 = 1 := by
  dsimp [vladimirov_psi]
  have h_bump : (vladimirovCutoffBump n 1 Real.zero_lt_one 0 : ℝ) = 1 := by
    apply (vladimirovCutoffBump n 1 Real.zero_lt_one).one_of_mem_closedBall
    simp only [Metric.mem_closedBall, dist_self]
    exact zero_le_one
  rw [h_bump, vladimirov_kernel_zero_p_n]
  push_cast
  ring

lemma scaledMomentumN_zero (n : ℕ) :
    scaledMomentumN n 0 = 0 := by
  dsimp [scaledMomentumN]
  exact smul_zero _

lemma vladimirov_fourier_eval_zero_n (n : ℕ) (z : Fin n → Fin 4 → ℂ) :
    minkowskiFourier (invMinkowskiFourierCLM n
      (vladimirov_psi_schwartz n 1 Real.zero_lt_one z)) 0 = 1 := by
  rw [minkowskiFourier_invMinkowskiFourierCLM_all]
  rw [scaledMomentumN_zero]
  change vladimirov_psi n 1 Real.zero_lt_one z 0 = 1
  exact vladimirov_psi_zero_p_n n z

lemma minkowskiFourier_eval_zero_n (n : ℕ) (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    minkowskiFourier f 0 = ∫ x, f x := by
  dsimp [minkowskiFourier]
  have h_exp : (fun x : Fin n → Fin 4 → ℝ =>
      f x * Complex.exp (-(Complex.I *
        ((∑ k : Fin n, minkowskiInner (0 : Fin 4 → ℝ) (x k) : ℝ) : ℂ)))) =
      (fun x => f x) := by
    ext x
    have h_inner : (∑ k : Fin n, minkowskiInner (0 : Fin 4 → ℝ) (x k)) = 0 := by
      apply Finset.sum_eq_zero
      intro k _
      simp [minkowskiInner_explicit]
    rw [h_inner]
    push_cast
    ring_nf
    rw [Complex.exp_zero, mul_one]
  rw [h_exp]

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_H_eq_const_of_zero_fourier (W : WightmanFamily ι) (n : ℕ) (α : Fin n → ι)
    (h_zero : ∀ g : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ, minkowskiFourier g 0 = 0 → W n α g = 0)
    (z : Fin n → Fin 4 → ℂ) :
    vladimirov_H W n α z = vladimirov_H W n α 0 := by
  let f_z := invMinkowskiFourierCLM n (vladimirov_psi_schwartz n 1 Real.zero_lt_one z)
  let f_0 := invMinkowskiFourierCLM n (vladimirov_psi_schwartz n 1 Real.zero_lt_one 0)
  change W n α f_z = W n α f_0
  rw [← sub_eq_zero, ← map_sub]
  apply h_zero (f_z - f_0)
  rw [minkowskiFourier_sub, vladimirov_fourier_eval_zero_n,
      vladimirov_fourier_eval_zero_n, sub_self]

omit [Fintype ι] [DecidableEq ι] in
lemma W_n_eq_integral_of_zero_fourier (W : WightmanFamily ι) (n : ℕ) (α : Fin n → ι)
    (h_zero : ∀ g : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ, minkowskiFourier g 0 = 0 → W n α g = 0)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    W n α f = vladimirov_H W n α 0 * ∫ x, f x := by
  let g0 := invMinkowskiFourierCLM n (vladimirov_psi_schwartz n 1 Real.zero_lt_one 0)
  let c := ∫ x, f x
  let g := f - c • g0
  have h_f0 : minkowskiFourier g 0 = 0 := by
    dsimp [g]
    rw [minkowskiFourier_sub, minkowskiFourier_eval_zero_n, minkowskiFourier_eval_zero_n]
    have h_smul : (∫ x, (c • g0) x) = c * ∫ x, g0 x := integral_const_mul c _
    have h_g0_int : (∫ x, g0 x) = 1 := by
      rw [← minkowskiFourier_eval_zero_n, vladimirov_fourier_eval_zero_n]
    rw [h_smul, h_g0_int, mul_one]
    exact sub_self c
  have h_Wg : W n α g = 0 := h_zero g h_f0
  dsimp [g] at h_Wg
  rw [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at h_Wg
  rw [h_Wg, mul_comm]
  rfl

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_H_real_integral_eq_of_zero_fourier (W : WightmanFamily ι) (n : ℕ) (α : Fin n → ι)
    (h_zero : ∀ g : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ, minkowskiFourier g 0 = 0 → W n α g = 0)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    (∫ x : Fin n → Fin 4 → ℝ, vladimirov_H W n α (fun i k => (x i k : ℂ)) * f x) = W n α f := by
  have h_const : (fun x : Fin n → Fin 4 → ℝ =>
      vladimirov_H W n α (fun i k => (x i k : ℂ)) * f x) =
      (fun x => vladimirov_H W n α 0 * f x) := by
    ext x
    rw [vladimirov_H_eq_const_of_zero_fourier W n α h_zero]
  rw [h_const, integral_const_mul, W_n_eq_integral_of_zero_fourier W n α h_zero f]

lemma vladimirov_H_boundary_step (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (hspec : SpectrumCondition W) (hP : PoincareCovariant R W) (n : ℕ) (hn : ¬ n ≤ 1)
    (α : Fin n → ι) (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    (v : Fin 4 → ℝ) (hv : v ∈ forward_light_cone) :
    Tendsto (fun t : ℝ => ∫ x : Fin n → Fin 4 → ℝ,
        vladimirov_H W n α
          (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ)) * f x)
      (𝓝[>] 0) (𝓝 (W n α f)) := by
  have h_tend_real := vladimirov_H_tend_real R W hP n hn α f v hv
  have h_zero : ∀ g : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ, minkowskiFourier g 0 = 0 → W n α g = 0 :=
    fun g hg => hspec n α g (Or.inr hg)
  have h_real_eq := vladimirov_H_real_integral_eq_of_zero_fourier W n α h_zero f
  rw [h_real_eq] at h_tend_real
  exact h_tend_real

lemma vladimirov_H_real_integral_eq (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (hspec : SpectrumCondition W) (hP : PoincareCovariant R W) (n : ℕ) (α : Fin n → ι)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    (∫ x : Fin n → Fin 4 → ℝ, vladimirov_H W n α (fun i k => (x i k : ℂ)) * f x) = W n α f := by
  by_cases hn : n ≤ 1
  · exact vladimirov_H_real_eq_le_one R W hspec hP n hn α f
  · obtain ⟨v, hv⟩ := exists_mem_forward_light_cone
    have h_tend_real := vladimirov_H_tend_real R W hP n hn α f v hv
    have h_tend_W := vladimirov_H_boundary_step R W hspec hP n hn α f v hv
    exact vladimirov_H_real_eq_of_tendsto_unique W n α f v h_tend_real h_tend_W

lemma exists_g_for_real_eq (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (hspec : SpectrumCondition W) (hP : PoincareCovariant R W) (n : ℕ) (α : Fin n → ι)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    ∃ g : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ,
      (∀ p ∈ scaledComNeighborhood n 1 1, minkowskiFourier (g - f) p = 0) ∧
      (∫ x : Fin n → Fin 4 → ℝ, vladimirov_H W n α (fun i k => (x i k : ℂ)) * f x) = W n α g := by
  refine ⟨f, fun p _ => ?_, vladimirov_H_real_integral_eq R W hspec hP n α f⟩
  rw [sub_self, minkowskiFourier_zero]

lemma vladimirov_H_real_eq (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (hspec : SpectrumCondition W) (hP : PoincareCovariant R W) (n : ℕ) (_hn : ¬ n ≤ 1)
    (α : Fin n → ι) (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) :
    (∫ x : Fin n → Fin 4 → ℝ, vladimirov_H W n α (fun i k => (x i k : ℂ)) * f x) = W n α f :=
  vladimirov_H_real_integral_eq R W hspec hP n α f

lemma vladimirov_H_boundary (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (hspec : SpectrumCondition W) (hP : PoincareCovariant R W) (n : ℕ) (α : Fin n → ι)
    (f : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ) (v : Fin 4 → ℝ) (hv : v ∈ forward_light_cone) :
    Tendsto (fun t : ℝ => ∫ x : Fin n → Fin 4 → ℝ,
        vladimirov_H W n α
          (fun i k => (x i k : ℂ) + Complex.I * ((t * (i : ℕ) * v k : ℝ) : ℂ)) * f x)
      (𝓝[>] 0) (𝓝 (W n α f)) := by
  by_cases hn : n ≤ 1
  · interval_cases n
    · exact vladimirov_H_boundary_zero W α f v hv
    · exact vladimirov_H_boundary_one R W hP α f v hv
        (W_one_eq_integral R W hspec hP α f)
  · exact vladimirov_H_boundary_step R W hspec hP n hn α f v hv

noncomputable def vladimirovTubeExtension (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (hspec : SpectrumCondition W) (hP : PoincareCovariant R W) : TubeExtension W where
  H := vladimirov_H W
  analytic := vladimirov_H_analytic R W hspec hP
  boundary := vladimirov_H_boundary R W hspec hP

omit [Fintype ι] [DecidableEq ι] in
lemma minkowskiFourier_diff_eval (n : ℕ) (A : SL2C) (z : Fin n → Fin 4 → ℂ)
    (f_z f1 f2 : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ)
    (hf_z : f_z = invMinkowskiFourierCLM n (vladimirov_psi_schwartz n 1 Real.zero_lt_one z))
    (hf1 : f1 = invMinkowskiFourierCLM n
      (vladimirov_psi_schwartz n 1 Real.zero_lt_one (spinorPhi (A, sl2c_conj A) • z)))
    (hf2 : f2 = schwartzLorentzCLM n A⁻¹ f_z)
    (p : Fin n → Fin 4 → ℝ) :
    minkowskiFourier (f1 - f2) p =
      vladimirov_psi n 1 Real.zero_lt_one (spinorPhi (A, sl2c_conj A) • z) (scaledMomentumN n p) -
      vladimirov_psi n 1 Real.zero_lt_one z ((lorentzEquiv n A⁻¹) (scaledMomentumN n p)) := by
  subst hf1 hf2 hf_z
  rw [minkowskiFourier_sub]
  rw [minkowskiFourier_schwartzLorentzCLM_n]
  rw [minkowskiFourier_invMinkowskiFourierCLM_all]
  rw [minkowskiFourier_invMinkowskiFourierCLM_all]
  have h_lorentz := scaledMomentumN_lorentz n A p
  rw [h_lorentz]
  rfl

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirov_kernel_ne_zero (n : ℕ) (z : Fin n → Fin 4 → ℂ) (p : Fin n → Fin 4 → ℝ) :
    vladimirov_kernel n z p ≠ 0 := by
  dsimp [vladimirov_kernel]
  exact Complex.exp_ne_zero _

omit [Fintype ι] [DecidableEq ι] in
lemma mul_kernel_eq_zero_iff (n : ℕ) (z : Fin n → Fin 4 → ℂ) (p : Fin n → Fin 4 → ℝ) (c : ℂ) :
    c * vladimirov_kernel n z p = 0 ↔ c = 0 := by
  have h_ne := vladimirov_kernel_ne_zero n z p
  exact mul_eq_zero_iff_right h_ne

omit [Fintype ι] [DecidableEq ι] in
lemma cutoffBump_diff_complex_eq_zero_iff (a b : ℝ) :
    ((a : ℂ) - (b : ℂ) = 0) ↔ a = b := by
  rw [sub_eq_zero, Complex.ofReal_inj]

omit [Fintype ι] [DecidableEq ι] in
lemma norm_fin1_eq (q : Fin 1 → Fin 4 → ℝ) : ‖q‖ = ‖q 0‖ := by
  have hpos : 0 ≤ ‖q 0‖ := norm_nonneg _
  apply le_antisymm
  · rw [pi_norm_le_iff_of_nonneg hpos]
    intro i
    fin_cases i
    exact le_rfl
  · exact norm_le_pi_norm q 0

omit [Fintype ι] [DecidableEq ι] in
lemma total_momentum_LM_one (q : Fin 1 → Fin 4 → ℝ) :
    total_momentum_LM 1 q = q 0 := by
  dsimp [total_momentum_LM]
  rw [Fin.sum_univ_one]

omit [Fintype ι] [DecidableEq ι] in
lemma mem_comNeighborhood_subset_cutoffNeighborhood (n : ℕ) (A : SL2C) (q : Fin n → Fin 4 → ℝ)
    (hq : q ∈ comNeighborhood n A 1) :
    q ∈ cutoffNeighborhood n A :=
  ⟨hq.2.2.1, hq.2.2.2⟩

omit [Fintype ι] [DecidableEq ι] in
lemma mem_comNeighborhood_one_iff (A : SL2C) (q : Fin 1 → Fin 4 → ℝ) :
    q ∈ comNeighborhood 1 A 1 ↔ q ∈ cutoffNeighborhood 1 A := by
  dsimp [comNeighborhood, cutoffNeighborhood]
  rw [Set.mem_inter_iff, Set.mem_preimage]
  simp only [Metric.mem_ball, dist_zero_right, total_momentum_LM_one]
  have h1 : ‖q 0‖ = ‖q‖ := (norm_fin1_eq q).symm
  have h2 : ‖(lorentzOfSL2C A⁻¹).mulVec (q 0)‖ = ‖(lorentzEquiv 1 A⁻¹) q‖ := by
    rw [norm_fin1_eq (lorentzEquiv 1 A⁻¹ q)]
    rfl
  rw [h1, h2]
  tauto

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirovCutoffBump_diff_one (A : SL2C) (p : Fin 1 → Fin 4 → ℝ)
    (hp : p ∈ scaledComNeighborhood 1 A 1) :
    vladimirovCutoffBump 1 1 Real.zero_lt_one (scaledMomentumN 1 p) =
    vladimirovCutoffBump 1 1 Real.zero_lt_one ((lorentzEquiv 1 A⁻¹) (scaledMomentumN 1 p)) := by
  have hp_cut : scaledMomentumN 1 p ∈ cutoffNeighborhood 1 A :=
    mem_comNeighborhood_subset_cutoffNeighborhood 1 A (scaledMomentumN 1 p) hp
  have ⟨h1, h2⟩ := cutoff_eq_one_in_neighborhood_gen 1 A (scaledMomentumN 1 p) hp_cut
  rw [h1, h2]

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirovCutoffBump_diff_of_mem_cutoffNeighborhood (n : ℕ) (A : SL2C)
    (q : Fin n → Fin 4 → ℝ) (hq : q ∈ cutoffNeighborhood n A) :
    vladimirovCutoffBump n 1 Real.zero_lt_one q =
    vladimirovCutoffBump n 1 Real.zero_lt_one ((lorentzEquiv n A⁻¹) q) := by
  have ⟨h1, h2⟩ := cutoff_eq_one_in_neighborhood_gen n A q hq
  rw [h1, h2]

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirovCutoffBump_diff_of_two_le (n : ℕ) (A : SL2C) (q : Fin n → Fin 4 → ℝ)
    (h1 : 2 ≤ ‖q‖) (h2 : 2 ≤ ‖(lorentzEquiv n A⁻¹) q‖) :
    vladimirovCutoffBump n 1 Real.zero_lt_one q =
    vladimirovCutoffBump n 1 Real.zero_lt_one ((lorentzEquiv n A⁻¹) q) := by
  rw [vladimirovCutoffBump_eq_zero_of_two_le n q h1]
  rw [vladimirovCutoffBump_eq_zero_of_two_le n ((lorentzEquiv n A⁻¹) q) h2]

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirovCutoffBump_diff_bound (n : ℕ) (q1 q2 : Fin n → Fin 4 → ℝ) :
    |vladimirovCutoffBump n 1 Real.zero_lt_one q1 -
     vladimirovCutoffBump n 1 Real.zero_lt_one q2| ≤ 1 := by
  have h1 := vladimirovCutoffBump_nonneg_and_le_one n q1
  have h2 := vladimirovCutoffBump_nonneg_and_le_one n q2
  rw [abs_le]
  constructor <;> linarith

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirovCutoffBump_diff_eq_of_sub_zero (n : ℕ) (q1 q2 : Fin n → Fin 4 → ℝ)
    (h_sub : vladimirovCutoffBump n 1 Real.zero_lt_one q1 -
             vladimirovCutoffBump n 1 Real.zero_lt_one q2 = 0) :
    vladimirovCutoffBump n 1 Real.zero_lt_one q1 = vladimirovCutoffBump n 1 Real.zero_lt_one q2 :=
  sub_eq_zero.mp h_sub

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirovCutoffBump_diff_ge_two_intermediate_sub (n : ℕ) (_hn : ¬ n ≤ 1)
    (A : SL2C) (p : Fin n → Fin 4 → ℝ)
    (hp : p ∈ scaledComNeighborhood n A 1)
    (h_not_in_cut : scaledMomentumN n p ∉ cutoffNeighborhood n A)
    (_h_not_both_ge_two :
      ¬ (2 ≤ ‖scaledMomentumN n p‖ ∧ 2 ≤ ‖(lorentzEquiv n A⁻¹) (scaledMomentumN n p)‖)) :
    vladimirovCutoffBump n 1 Real.zero_lt_one (scaledMomentumN n p) -
    vladimirovCutoffBump n 1 Real.zero_lt_one
      ((lorentzEquiv n A⁻¹) (scaledMomentumN n p)) = 0 :=
  False.elim (h_not_in_cut (mem_comNeighborhood_subset_cutoffNeighborhood n A _ hp))

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirovCutoffBump_diff_ge_two_intermediate (n : ℕ) (hn : ¬ n ≤ 1)
    (A : SL2C) (p : Fin n → Fin 4 → ℝ)
    (hp : p ∈ scaledComNeighborhood n A 1)
    (h_not_in_cut : scaledMomentumN n p ∉ cutoffNeighborhood n A)
    (h_not_both_ge_two :
      ¬ (2 ≤ ‖scaledMomentumN n p‖ ∧ 2 ≤ ‖(lorentzEquiv n A⁻¹) (scaledMomentumN n p)‖)) :
    vladimirovCutoffBump n 1 Real.zero_lt_one (scaledMomentumN n p) =
    vladimirovCutoffBump n 1 Real.zero_lt_one ((lorentzEquiv n A⁻¹) (scaledMomentumN n p)) := by
  exact vladimirovCutoffBump_diff_eq_of_sub_zero n _ _
    (vladimirovCutoffBump_diff_ge_two_intermediate_sub n hn A p hp h_not_in_cut h_not_both_ge_two)

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirovCutoffBump_diff_ge_two (n : ℕ) (hn : ¬ n ≤ 1)
    (A : SL2C) (p : Fin n → Fin 4 → ℝ)
    (hp : p ∈ scaledComNeighborhood n A 1) :
    vladimirovCutoffBump n 1 Real.zero_lt_one (scaledMomentumN n p) =
    vladimirovCutoffBump n 1 Real.zero_lt_one ((lorentzEquiv n A⁻¹) (scaledMomentumN n p)) := by
  let q := scaledMomentumN n p
  by_cases hq : q ∈ cutoffNeighborhood n A
  · exact vladimirovCutoffBump_diff_of_mem_cutoffNeighborhood n A q hq
  · by_cases h2 : 2 ≤ ‖q‖ ∧ 2 ≤ ‖(lorentzEquiv n A⁻¹) q‖
    · exact vladimirovCutoffBump_diff_of_two_le n A q h2.1 h2.2
    · exact vladimirovCutoffBump_diff_ge_two_intermediate n hn A p hp hq h2

omit [Fintype ι] [DecidableEq ι] in
lemma vladimirovCutoffBump_lorentz_diff_mul_kernel_zero
    (n : ℕ) (A : SL2C) (z : Fin n → Fin 4 → ℂ) (p : Fin n → Fin 4 → ℝ)
    (hp : p ∈ scaledComNeighborhood n A 1) :
    (((vladimirovCutoffBump n 1 Real.zero_lt_one (scaledMomentumN n p) : ℝ) : ℂ) -
     ((vladimirovCutoffBump n 1 Real.zero_lt_one
         ((lorentzEquiv n A⁻¹) (scaledMomentumN n p)) : ℝ) : ℂ)) *
      vladimirov_kernel n z ((lorentzEquiv n A⁻¹) (scaledMomentumN n p)) = 0 := by
  rw [mul_kernel_eq_zero_iff]
  rw [cutoffBump_diff_complex_eq_zero_iff]
  by_cases hn : n ≤ 1
  · interval_cases n
    · have hp0 : scaledMomentumN 0 p = 0 := Subsingleton.elim _ 0
      rw [hp0]
      have h_map : (lorentzEquiv 0 A⁻¹) 0 = 0 := map_zero (lorentzEquiv 0 A⁻¹)
      rw [h_map]
    · exact vladimirovCutoffBump_diff_one A p hp
  · exact vladimirovCutoffBump_diff_ge_two n hn A p hp

lemma vladimirov_tubeCovariant (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (hspec : SpectrumCondition W) (hP : PoincareCovariant R W) :
    TubeCovariant R (vladimirovTubeExtension R W hspec hP) := by
  intro n A z hz hz_trans α
  dsimp [vladimirovTubeExtension, vladimirov_H, vladimirov_H_cutoff]
  let f_z : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ :=
    invMinkowskiFourierCLM n (vladimirov_psi_schwartz n 1 Real.zero_lt_one z)
  have h_cov := wightman_lorentz_cov R W hP n A f_z α
  rw [← h_cov]
  by_cases hn : n ≤ 1
  · exact vladimirov_cutoff_lorentz_diff W hspec n hn A z α
  · let f1 := invMinkowskiFourierCLM n
      (vladimirov_psi_schwartz n 1 Real.zero_lt_one (spinorPhi (A, sl2c_conj A) • z))
    let f2 := schwartzLorentzCLM n A⁻¹ f_z
    rw [← sub_eq_zero]
    apply close_lorentz_cov_step W hspec n A α f1 f2
    intro p hp
    rw [minkowskiFourier_diff_eval n A z f_z f1 f2 rfl rfl rfl p]
    have hp_com : scaledMomentumN n p ∈ comNeighborhood n A 1 := hp
    have h_com := vladimirov_psi_com_lorentz_diff_zero n A 1 Real.zero_lt_one z
      (scaledMomentumN n p) hp_com
    have ⟨h_c1, h_c2⟩ := comCutoff_lorentz_eq_one n A 1 Real.zero_lt_one
      (scaledMomentumN n p) hp_com
    dsimp [vladimirov_psi_com] at h_com
    rw [h_c1, h_c2] at h_com
    push_cast at h_com
    rw [one_mul, one_mul] at h_com
    have _h_ker_eq : vladimirov_kernel n (spinorPhi (A, sl2c_conj A) • z)
      (scaledMomentumN n p) =
      vladimirov_kernel n z ((lorentzEquiv n A⁻¹) (scaledMomentumN n p)) :=
      sub_eq_zero.mp h_com
    change vladimirov_psi n 1 Real.zero_lt_one (spinorPhi (A, sl2c_conj A) • z)
             (scaledMomentumN n p) -
           vladimirov_psi n 1 Real.zero_lt_one z
             ((lorentzEquiv n A⁻¹) (scaledMomentumN n p)) = 0
    dsimp [vladimirov_psi]
    rw [_h_ker_eq]
    have h_factor :
      ((vladimirovCutoffBump n 1 Real.zero_lt_one (scaledMomentumN n p) : ℝ) : ℂ) *
        vladimirov_kernel n z ((lorentzEquiv n A⁻¹) (scaledMomentumN n p)) -
      ((vladimirovCutoffBump n 1 Real.zero_lt_one
          ((lorentzEquiv n A⁻¹) (scaledMomentumN n p)) : ℝ) : ℂ) *
        vladimirov_kernel n z ((lorentzEquiv n A⁻¹) (scaledMomentumN n p)) =
      (((vladimirovCutoffBump n 1 Real.zero_lt_one (scaledMomentumN n p) : ℝ) : ℂ) -
       ((vladimirovCutoffBump n 1 Real.zero_lt_one
           ((lorentzEquiv n A⁻¹) (scaledMomentumN n p)) : ℝ) : ℂ)) *
        vladimirov_kernel n z ((lorentzEquiv n A⁻¹) (scaledMomentumN n p)) := by ring
    rw [h_factor]
    exact vladimirovCutoffBump_lorentz_diff_mul_kernel_zero n A z p hp

theorem exists_tube_extension (R : HolomorphicLorentzRep ι) (W : WightmanFamily ι)
    (hspec : SpectrumCondition W) (hP : PoincareCovariant R W) :
    ∃ E : TubeExtension W, TubeCovariant R E :=
  ⟨vladimirovTubeExtension R W hspec hP, vladimirov_tubeCovariant R W hspec hP⟩

end QFT
