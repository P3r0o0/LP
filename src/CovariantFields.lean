import Mathlib.Analysis.Distribution.TemperedDistribution
import Mathlib.Algebra.MvPolynomial.Eval
import Minkowski
import Spinor
import MatrixAnalysis



namespace QFT

open Geometry Geometry.MatrixAnalysis Matrix


abbrev SL2C : Type := SpecialLinearGroup (Fin 2) ℂ


noncomputable def sl2cConjHom : SL2C →* SL2C where
  toFun := sl2c_conj
  map_one' := sl2c_conj_one
  map_mul' := sl2c_conj_mul


lemma sl2c_conj_conj (A : SL2C) : sl2c_conj (sl2c_conj A) = A := by
  apply Subtype.ext
  ext i j
  simp [sl2c_conj]


structure HolomorphicLorentzRep (ι : Type*) [Fintype ι] [DecidableEq ι] where
  σ : SL2C × SL2C →* Matrix ι ι ℂ
  polynomial : ∀ i j : ι, ∃ P : MvPolynomial ((Fin 2 × Fin 2) ⊕ (Fin 2 × Fin 2)) ℂ,
    ∀ p : SL2C × SL2C,
      σ p i j = MvPolynomial.eval
        (Sum.elim (fun a => (p.1 : Matrix (Fin 2) (Fin 2) ℂ) a.1 a.2)
                  (fun a => (p.2 : Matrix (Fin 2) (Fin 2) ℂ) a.1 a.2)) P

namespace HolomorphicLorentzRep

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


noncomputable def rep (R : HolomorphicLorentzRep ι) : SL2C →* Matrix ι ι ℂ :=
  R.σ.comp ((MonoidHom.id SL2C).prod sl2cConjHom)

lemma rep_apply (R : HolomorphicLorentzRep ι) (A : SL2C) : R.rep A = R.σ (A, sl2c_conj A) := rfl


lemma σ_neg_one_sq (R : HolomorphicLorentzRep ι) :
    R.σ ((-1 : SL2C), (-1 : SL2C)) * R.σ ((-1 : SL2C), (-1 : SL2C)) = 1 := by
  rw [← map_mul]
  have h : ((-1 : SL2C), (-1 : SL2C)) * ((-1 : SL2C), (-1 : SL2C)) = 1 := by
    refine Prod.ext ?_ ?_ <;>
    · apply Subtype.ext
      change (-1 : Matrix (Fin 2) (Fin 2) ℂ) * -1 = 1
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.one_apply]
  rw [h, map_one]


def HasSpinParity (R : HolomorphicLorentzRep ι) (ε : ℂ) : Prop :=
  R.σ ((-1 : SL2C), (-1 : SL2C)) = ε • (1 : Matrix ι ι ℂ) ∧ (ε = 1 ∨ ε = -1)

end HolomorphicLorentzRep


noncomputable def lorentzOfSL2C (A : SL2C) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun i j => ((spinorPhi (A, sl2c_conj A) : SpecialSpecialComplexLorentzGroup).val.val i j).re


lemma spinorPhi_conj_real (A : SL2C) :
    Matrix.map (spinorPhi (A, sl2c_conj A)).val.val star = (spinorPhi (A, sl2c_conj A)).val.val := by
  rw [spinorPhi_conj A (sl2c_conj A), sl2c_conj_conj]


lemma lorentzOfSL2C_map (A : SL2C) :
    (lorentzOfSL2C A).map (algebraMap ℝ ℂ) = (spinorPhi (A, sl2c_conj A)).val.val := by
  ext i j
  have h := congrFun (congrFun (spinorPhi_conj_real A) i) j
  simp only [Matrix.map_apply] at h ⊢
  change ((((spinorPhi (A, sl2c_conj A)).val.val i j).re : ℝ) : ℂ) = _
  apply Complex.ext
  · simp
  · have him := congrArg Complex.im h
    simp at him
    simp
    linarith


noncomputable def poincareAct (a : Fin 4 → ℝ) (A : SL2C) (x : Fin 4 → ℝ) : Fin 4 → ℝ :=
  (lorentzOfSL2C A).mulVec x + a

open SchwartzMap in

def PoincareCovariant {ι : Type*} [Fintype ι] [DecidableEq ι] (R : HolomorphicLorentzRep ι)
    (W : ∀ n : ℕ, (Fin n → ι) → TemperedDistribution (Fin n → Fin 4 → ℝ) ℂ) : Prop :=
  ∀ (n : ℕ) (a : Fin 4 → ℝ) (A : SL2C)
    (f f' : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ),
    (∀ x : Fin n → Fin 4 → ℝ, f' (fun i => poincareAct a A (x i)) = f x) →
    ∀ α : Fin n → ι,
      W n α f' = ∑ β : Fin n → ι, (∏ i, R.rep A (α i) (β i)) * W n β f




abbrev PolyVar : Type := (Fin 2 × Fin 2) ⊕ (Fin 2 × Fin 2)


noncomputable def polyPt (p : SL2C × SL2C) : PolyVar → ℂ :=
  Sum.elim (fun a => (p.1 : Matrix (Fin 2) (Fin 2) ℂ) a.1 a.2)
           (fun a => (p.2 : Matrix (Fin 2) (Fin 2) ℂ) a.1 a.2)


def IsPoly (f : SL2C × SL2C → ℂ) : Prop :=
  ∃ P : MvPolynomial PolyVar ℂ, ∀ p, f p = MvPolynomial.eval (polyPt p) P

namespace IsPoly

lemma const (c : ℂ) : IsPoly fun _ => c :=
  ⟨MvPolynomial.C c, fun p => by simp⟩

lemma coordA (i j : Fin 2) : IsPoly fun p => (p.1 : Matrix (Fin 2) (Fin 2) ℂ) i j :=
  ⟨MvPolynomial.X (Sum.inl (i, j)), fun p => by simp [polyPt]⟩

lemma coordB (i j : Fin 2) : IsPoly fun p => (p.2 : Matrix (Fin 2) (Fin 2) ℂ) i j :=
  ⟨MvPolynomial.X (Sum.inr (i, j)), fun p => by simp [polyPt]⟩

lemma add {f g : SL2C × SL2C → ℂ} (hf : IsPoly f) (hg : IsPoly g) :
    IsPoly fun p => f p + g p := by
  obtain ⟨P, hP⟩ := hf
  obtain ⟨Q, hQ⟩ := hg
  exact ⟨P + Q, fun p => by simp [hP p, hQ p]⟩

lemma sub {f g : SL2C × SL2C → ℂ} (hf : IsPoly f) (hg : IsPoly g) :
    IsPoly fun p => f p - g p := by
  obtain ⟨P, hP⟩ := hf
  obtain ⟨Q, hQ⟩ := hg
  exact ⟨P - Q, fun p => by simp [hP p, hQ p]⟩

lemma mul {f g : SL2C × SL2C → ℂ} (hf : IsPoly f) (hg : IsPoly g) :
    IsPoly fun p => f p * g p := by
  obtain ⟨P, hP⟩ := hf
  obtain ⟨Q, hQ⟩ := hg
  exact ⟨P * Q, fun p => by simp [hP p, hQ p]⟩

lemma div_const {f : SL2C × SL2C → ℂ} (hf : IsPoly f) (c : ℂ) :
    IsPoly fun p => f p / c := by
  obtain ⟨P, hP⟩ := hf
  exact ⟨P * MvPolynomial.C c⁻¹, fun p => by simp [hP p, div_eq_mul_inv]⟩

lemma sum {ι : Type*} (s : Finset ι) (f : ι → SL2C × SL2C → ℂ)
    (h : ∀ i ∈ s, IsPoly (f i)) : IsPoly fun p => ∑ i ∈ s, f i p := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (by simp)).add (ih fun i hi => h i (by simp [hi]))

end IsPoly


lemma isPoly_entry_ASBt (X : Matrix (Fin 2) (Fin 2) ℂ) (a b : Fin 2) :
    IsPoly fun p => ((p.1 : Matrix (Fin 2) (Fin 2) ℂ) * X * (p.2 : Matrix (Fin 2) (Fin 2) ℂ)ᵀ) a b := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  exact IsPoly.sum _ _ fun k _ =>
    (IsPoly.sum _ _ fun l _ => (IsPoly.coordA a l).mul (IsPoly.const (X l k))).mul
      (IsPoly.coordB b k)


lemma isPoly_spinor_to_vec (F : SL2C × SL2C → Matrix (Fin 2) (Fin 2) ℂ)
    (hF : ∀ a b, IsPoly fun p => F p a b) (i : Fin 4) :
    IsPoly fun p => spinor_to_vec (F p) i := by
  fin_cases i
  · exact ((hF 0 0).add (hF 1 1)).div_const 2
  · exact ((hF 0 1).add (hF 1 0)).div_const 2
  · exact (((hF 0 1).sub (hF 1 0)).mul (IsPoly.const Complex.I)).div_const 2
  · exact ((hF 0 0).sub (hF 1 1)).div_const 2


lemma isPoly_spinorPhi_matrix (i j : Fin 4) :
    IsPoly fun p => spinorPhi_matrix p.1 p.2 i j := by
  have h : (fun p : SL2C × SL2C => spinorPhi_matrix p.1 p.2 i j) =
      fun p => spinor_to_vec
        ((p.1 : Matrix (Fin 2) (Fin 2) ℂ) * vec_to_spinor (fun k => if k = j then 1 else 0) *
          (p.2 : Matrix (Fin 2) (Fin 2) ℂ)ᵀ) i := by
    funext p
    rw [spinorPhi_matrix_apply]
    rfl
  rw [h]
  exact isPoly_spinor_to_vec
    (fun p : SL2C × SL2C => (p.1 : Matrix (Fin 2) (Fin 2) ℂ) *
      vec_to_spinor (fun k => if k = j then 1 else 0) * (p.2 : Matrix (Fin 2) (Fin 2) ℂ)ᵀ)
    (fun a b => isPoly_entry_ASBt _ a b) i




noncomputable def trivialRep : HolomorphicLorentzRep Unit where
  σ := 1
  polynomial i j := ⟨MvPolynomial.C 1, fun p => by simp⟩

lemma trivialRep_spinParity : trivialRep.HasSpinParity 1 := by
  refine ⟨?_, Or.inl rfl⟩
  rw [one_smul]
  rfl


lemma trivialRep_covariant_iff
    (W : ∀ n : ℕ, (Fin n → Unit) → TemperedDistribution (Fin n → Fin 4 → ℝ) ℂ) :
    PoincareCovariant trivialRep W ↔
      ∀ (n : ℕ) (a : Fin 4 → ℝ) (A : SL2C) (f f' : SchwartzMap (Fin n → Fin 4 → ℝ) ℂ),
        (∀ x : Fin n → Fin 4 → ℝ, f' (fun i => poincareAct a A (x i)) = f x) →
        ∀ α : Fin n → Unit, W n α f' = W n α f := by
  have key : ∀ (n : ℕ) (A : SL2C) (α β : Fin n → Unit),
      (∏ i, trivialRep.rep A (α i) (β i)) = 1 := by
    intro n A α β
    apply Finset.prod_eq_one
    intro i _
    simp [HolomorphicLorentzRep.rep_apply, trivialRep]
  constructor
  · intro h n a A f f' hf α
    rw [h n a A f f' hf α, Fintype.sum_unique, key n A α default, one_mul,
      Subsingleton.elim (default : Fin n → Unit) α]
  · intro h n a A f f' hf α
    rw [h n a A f f' hf α, Fintype.sum_unique, key n A α default, one_mul,
      Subsingleton.elim (default : Fin n → Unit) α]




noncomputable def stdRep : HolomorphicLorentzRep (Fin 4) where
  σ := (Units.coeHom (Matrix (Fin 4) (Fin 4) ℂ)).comp
    ((Subgroup.subtype SpecialSpecialComplexLorentzGroup).comp spinorPhi)
  polynomial i j := by
    obtain ⟨P, hP⟩ := isPoly_spinorPhi_matrix i j
    exact ⟨P, fun p => hP p⟩


lemma stdRep_rep (A : SL2C) :
    stdRep.rep A = (lorentzOfSL2C A).map (algebraMap ℝ ℂ) := by
  rw [lorentzOfSL2C_map]
  rfl

lemma stdRep_spinParity : stdRep.HasSpinParity 1 := by
  refine ⟨?_, Or.inl rfl⟩
  rw [one_smul]
  have h : ∀ x : Fin 4 → ℂ,
      spinor_action ((-1 : SL2C) : Matrix (Fin 2) (Fin 2) ℂ)
        ((-1 : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) x = x := by
    intro x
    have e : ((-1 : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) * vec_to_spinor x *
        ((-1 : SL2C) : Matrix (Fin 2) (Fin 2) ℂ)ᵀ = vec_to_spinor x := by
      simp [Matrix.SpecialLinearGroup.coe_neg]
    simp only [spinor_action]
    rw [e, spinor_to_vec_left_inv]
  ext i j
  change spinorPhi_matrix (-1) (-1) i j = (1 : Matrix (Fin 4) (Fin 4) ℂ) i j
  rw [spinorPhi_matrix_apply, h]
  simp [Matrix.one_apply]




noncomputable def leftWeylRep : HolomorphicLorentzRep (Fin 2) where
  σ :=
    { toFun := fun p => (p.1 : Matrix (Fin 2) (Fin 2) ℂ)
      map_one' := by simp
      map_mul' := fun p q => by simp }
  polynomial i j := ⟨MvPolynomial.X (Sum.inl (i, j)), fun p => by simp⟩


lemma leftWeylRep_spinParity : leftWeylRep.HasSpinParity (-1) := by
  refine ⟨?_, Or.inr rfl⟩
  change ((-1 : SL2C) : Matrix (Fin 2) (Fin 2) ℂ) = (-1 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
  simp [Matrix.SpecialLinearGroup.coe_neg]

end QFT
