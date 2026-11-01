import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin

namespace LWE

section Generic

variable (R : Type*) [CommRing R]

abbrev VectorR (len : ℕ) := Fin len → R

abbrev MatrixR (n m : ℕ) := Matrix (Fin m) (Fin n) R

open scoped BigOperators

def evaluate (n m : ℕ) (A : MatrixR R n m) (s : VectorR R n) (e : VectorR R m) : VectorR R m :=
  fun i => (∑ j, A i j * s j) + e i

structure Sample (n m : ℕ) where
  A : MatrixR R n m
  b : VectorR R m

def mkSample (n m : ℕ) (A : MatrixR R n m) (s : VectorR R n) (e : VectorR R m) : Sample R n m :=
  { A := A, b := evaluate R n m A s e }

def addSamples {n m : ℕ} (c1 c2 : Sample R n m) : Sample R n m :=
  { A := c1.A + c2.A,
    b := c1.b + c2.b }

theorem addSamples_correct {n m : ℕ} (s : VectorR R n) (A1 A2 : MatrixR R n m)
    (e1 e2 : VectorR R m) :
    addSamples R (mkSample R n m A1 s e1) (mkSample R n m A2 s e2) =
    mkSample R n m (A1 + A2) s (e1 + e2) := by
  dsimp [addSamples, mkSample]
  congr 1
  ext i
  simp [evaluate, add_mul, Finset.sum_add_distrib]
  ring

end Generic

section Zq

structure LWEParams where
  n : ℕ
  m : ℕ
  q : ℕ
  [q_pos : Fact (0 < q)]

variable (params : LWEParams)

abbrev Zq := ZMod params.q

def centeredLift (x : Zq params) : ℤ :=
  let val : ℤ := ZMod.val x
  let q_int : ℤ := params.q
  if val ≤ q_int / 2 then
    val
  else
    val - q_int

def norm (x : Zq params) : ℕ :=
  (centeredLift params x).natAbs

def normInf {len : ℕ} (v : VectorR (Zq params) len) : ℕ :=
  Finset.sup Finset.univ (fun i => norm params (v i))

lemma val_lt (x : Zq params) : (ZMod.val x : ℤ) < params.q := by
  haveI : NeZero params.q := ⟨ne_of_gt params.q_pos.out⟩
  have h := ZMod.val_lt x
  exact_mod_cast h

lemma val_nonneg (x : Zq params) : 0 ≤ (ZMod.val x : ℤ) := by
  exact Int.natCast_nonneg (ZMod.val x)

lemma val_add_cases (x y : Zq params) :
    (ZMod.val (x + y) : ℤ) = (ZMod.val x : ℤ) + (ZMod.val y : ℤ) ∨
    (ZMod.val (x + y) : ℤ) = (ZMod.val x : ℤ) + (ZMod.val y : ℤ) - params.q := by
  haveI : NeZero params.q := ⟨ne_of_gt params.q_pos.out⟩
  have h_add := ZMod.val_add x y
  have hx := ZMod.val_lt x
  have hy := ZMod.val_lt y
  by_cases h : ZMod.val x + ZMod.val y < params.q
  · left
    rw [h_add, Nat.mod_eq_of_lt h]
    push_cast
    rfl
  · right
    have h_le : params.q ≤ ZMod.val x + ZMod.val y := by omega
    have h_mod := Nat.mod_eq_sub_mod h_le
    rw [h_add, h_mod]
    have h_lt : ZMod.val x + ZMod.val y - params.q < params.q := by omega
    rw [Nat.mod_eq_of_lt h_lt]
    rw [Nat.cast_sub h_le]
    push_cast
    rfl

theorem norm_add_le_elem (params : LWEParams) (x y : Zq params) :
    norm params (x + y) ≤ norm params x + norm params y := by
  have h_cases := val_add_cases params x y
  have hq_pos : 0 < (params.q : ℤ) := by exact_mod_cast params.q_pos.out
  have hx_lt := val_lt params x
  have hy_lt := val_lt params y
  have hxy_lt := val_lt params (x + y)
  have hx_ge := val_nonneg params x
  have hy_ge := val_nonneg params y
  have hxy_ge := val_nonneg params (x + y)
  generalize hcxy : centeredLift params (x + y) = cxy
  generalize hcx : centeredLift params x = cx
  generalize hcy : centeredLift params y = cy
  unfold norm
  rw [hcxy, hcx, hcy]
  unfold centeredLift at hcxy hcx hcy
  dsimp at hcxy hcx hcy
  rcases h_cases with h_add | h_add
  · rw [h_add] at hcxy
    split_ifs at hcxy hcx hcy <;> omega
  · rw [h_add] at hcxy
    split_ifs at hcxy hcx hcy <;> omega

theorem norm_add_le {len : ℕ} (e1 e2 : VectorR (Zq params) len) :
    normInf params (e1 + e2) ≤ normInf params e1 + normInf params e2 := by
  dsimp [normInf]
  apply Finset.sup_le
  intro i _
  have h_elem := norm_add_le_elem params (e1 i) (e2 i)
  have h_sup1 : norm params (e1 i) ≤ Finset.sup Finset.univ (fun j => norm params (e1 j)) :=
    Finset.le_sup (f := fun j => norm params (e1 j)) (Finset.mem_univ i)
  have h_sup2 : norm params (e2 i) ≤ Finset.sup Finset.univ (fun j => norm params (e2 j)) :=
    Finset.le_sup (f := fun j => norm params (e2 j)) (Finset.mem_univ i)
  omega

theorem norm_neg_elem (params : LWEParams) (x : Zq params) :
    norm params (-x) = norm params x := by
  haveI : NeZero params.q := ⟨ne_of_gt params.q_pos.out⟩
  have h_cases := val_add_cases params x (-x)
  rw [add_neg_cancel, ZMod.val_zero, Nat.cast_zero] at h_cases
  have hq_pos : 0 < (params.q : ℤ) := by exact_mod_cast params.q_pos.out
  have hx_lt := val_lt params x
  have hnx_lt := val_lt params (-x)
  have hx_ge := val_nonneg params x
  have hnx_ge := val_nonneg params (-x)
  unfold norm centeredLift
  dsimp
  rcases h_cases with h_sum | h_sum
  · split_ifs <;> omega
  · split_ifs <;> omega

theorem norm_sub_le_elem (params : LWEParams) (x y : Zq params) :
    norm params (x - y) ≤ norm params x + norm params y := by
  rw [sub_eq_add_neg, ← norm_neg_elem params y]
  exact norm_add_le_elem params x (-y)

theorem norm_neg {len : ℕ} (e : VectorR (Zq params) len) :
    normInf params (-e) = normInf params e := by
  dsimp [normInf]
  congr 1
  ext i
  exact norm_neg_elem params (e i)

theorem norm_sub_le {len : ℕ} (e1 e2 : VectorR (Zq params) len) :
    normInf params (e1 - e2) ≤ normInf params e1 + normInf params e2 := by
  rw [sub_eq_add_neg, ← norm_neg params e2]
  exact norm_add_le params e1 (-e2)

theorem norm_zero (params : LWEParams) : norm params 0 = 0 := by
  haveI : NeZero params.q := ⟨ne_of_gt params.q_pos.out⟩
  unfold norm centeredLift
  dsimp
  rw [ZMod.val_zero, Nat.cast_zero]
  split_ifs <;> omega

theorem norm_finset_sum_le (params : LWEParams) {ι : Type*} (s : Finset ι) (f : ι → Zq params) :
    norm params (∑ i ∈ s, f i) ≤ ∑ i ∈ s, norm params (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp [norm_zero]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have h_add := norm_add_le_elem params (f a) (∑ i ∈ s, f i)
    omega

def IsTernaryElem {R : Type*} [Ring R] (x : R) : Prop :=
  x = 0 ∨ x = 1 ∨ x = -1

theorem norm_ternary_mul_le (params : LWEParams) (c x : Zq params) (hc : IsTernaryElem c) :
    norm params (c * x) ≤ norm params x := by
  rcases hc with rfl | rfl | rfl
  · rw [zero_mul, norm_zero]
    exact Nat.zero_le _
  · rw [one_mul]
  · rw [neg_one_mul, norm_neg_elem]

end Zq

section RingLWE

variable {R : Type*} [CommRing R]

structure RingSample (R : Type*) [CommRing R] where
  a : R
  b : R

def mkRingSample (a s e : R) : RingSample R :=
  { a := a, b := a * s + e }

structure RingSample2 (R : Type*) [CommRing R] where
  d0 : R
  d1 : R
  d2 : R

def mulRingSamples (c1 c2 : RingSample R) : RingSample2 R :=
  { d0 := c1.b * c2.b,
    d1 := c1.a * c2.b + c2.a * c1.b,
    d2 := c1.a * c2.a }

theorem mulRingSamples_correct (s a1 a2 e1 e2 : R) :
    let c1 := mkRingSample a1 s e1
    let c2 := mkRingSample a2 s e2
    let c_mul := mulRingSamples c1 c2
    c_mul.d0 - c_mul.d1 * s + c_mul.d2 * (s * s) = e1 * e2 := by
  dsimp [mkRingSample, mulRingSamples]
  ring

structure RelinKey (R : Type*) [CommRing R] where
  a_rk : R
  b_rk : R

def mkRelinKey (a_rk s e_rk : R) : RelinKey R :=
  { a_rk := a_rk, b_rk := a_rk * s + e_rk + (s * s) }

def relinearize (c_mul : RingSample2 R) (rk : RelinKey R) : RingSample R :=
  { a := c_mul.d1 + c_mul.d2 * rk.a_rk,
    b := c_mul.d0 + c_mul.d2 * rk.b_rk }

theorem relinearize_correct (s a_rk e_rk d0 d1 d2 : R) :
    let rk := mkRelinKey a_rk s e_rk
    let c_mul : RingSample2 R := { d0 := d0, d1 := d1, d2 := d2 }
    let c_relin := relinearize c_mul rk
    c_relin.b - c_relin.a * s = (d0 - d1 * s + d2 * (s * s)) + d2 * e_rk := by
  dsimp [mkRelinKey, relinearize]
  ring

def IsValidDecomposition {l : ℕ} (G : VectorR R l) (decompose : R → VectorR R l) : Prop :=
  ∀ x : R, (∑ i : Fin l, decompose x i * G i) = x

structure GadgetRelinKey (R : Type*) [CommRing R] (l : ℕ) where
  a_rk : VectorR R l
  b_rk : VectorR R l

def mkGadgetRelinKey {l : ℕ} (a_rk e_rk : VectorR R l) (s : R) (G : VectorR R l) :
    GadgetRelinKey R l :=
  { a_rk := a_rk,
    b_rk := fun i => a_rk i * s + e_rk i + G i * (s * s) }

def gadgetRelinearize {l : ℕ} (c_mul : RingSample2 R) (decomp : R → VectorR R l)
    (rk : GadgetRelinKey R l) : RingSample R :=
  let d2_dec := decomp c_mul.d2
  { a := c_mul.d1 + (∑ i, d2_dec i * rk.a_rk i),
    b := c_mul.d0 + (∑ i, d2_dec i * rk.b_rk i) }

theorem gadgetRelinearize_correct {l : ℕ} (s d0 d1 d2 : R)
    (a_rk e_rk G : VectorR R l) (decomp : R → VectorR R l) (h_dec : IsValidDecomposition G decomp) :
    let rk := mkGadgetRelinKey a_rk e_rk s G
    let c_mul : RingSample2 R := { d0 := d0, d1 := d1, d2 := d2 }
    let c_relin := gadgetRelinearize c_mul decomp rk
    c_relin.b - c_relin.a * s = (d0 - d1 * s + d2 * (s * s)) + (∑ i, decomp d2 i * e_rk i) := by
  dsimp [mkGadgetRelinKey, gadgetRelinearize]
  simp only [mul_add, add_mul]
  simp only [Finset.sum_add_distrib]
  have h1 : (∑ i : Fin l, decomp d2 i * (a_rk i * s)) =
      (∑ i : Fin l, decomp d2 i * a_rk i) * s := by
    simp_rw [← mul_assoc, Finset.sum_mul]
  have h2 : (∑ i : Fin l, decomp d2 i * (G i * (s * s))) =
      (∑ i : Fin l, decomp d2 i * G i) * (s * s) := by
    simp_rw [← mul_assoc, Finset.sum_mul]
  rw [h1, h2, h_dec d2]
  ring

end RingLWE

section ConcreteGadget

open scoped BigOperators

theorem nat_base_decomp_sum (B : ℕ) :
    ∀ (l v : ℕ), v < B ^ l →
      (∑ i : Fin l, ((v / B ^ (i : ℕ)) % B) * B ^ (i : ℕ)) = v
  | 0, v, hv => by
    simp only [pow_zero, Nat.lt_one_iff] at hv
    subst hv
    simp
  | l + 1, v, hv => by
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, pow_zero, Nat.div_one, mul_one, Fin.val_succ]
    have hB_pos : 0 < B := by
      by_contra h
      have h0 : B = 0 := by omega
      rw [h0, zero_pow (Nat.succ_ne_zero l)] at hv
      omega
    have hv_div : v / B < B ^ l := by
      apply Nat.div_lt_of_lt_mul
      simpa [pow_succ'] using hv
    have h_tail :
        (∑ i : Fin l, ((v / B ^ ((i : ℕ) + 1)) % B) * B ^ ((i : ℕ) + 1)) =
        (∑ i : Fin l, (((v / B) / B ^ (i : ℕ)) % B) * B ^ (i : ℕ)) * B := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [pow_succ', ← Nat.div_div_eq_div_mul, mul_comm B (B ^ (i : ℕ)), ← mul_assoc]
    rw [h_tail, nat_base_decomp_sum B l (v / B) hv_div]
    have h_div := Nat.mod_add_div v B
    have h_comm : B * (v / B) = v / B * B := Nat.mul_comm B (v / B)
    omega

variable (params : LWEParams)

def baseGadget (B l : ℕ) : VectorR (Zq params) l :=
  fun i => ((B ^ (i : ℕ) : ℕ) : Zq params)

def baseDecomp (B l : ℕ) (x : Zq params) : VectorR (Zq params) l :=
  fun i => ((((ZMod.val x) / B ^ (i : ℕ)) % B : ℕ) : Zq params)

theorem baseDecomp_isValid (B l : ℕ) (hq : params.q ≤ B ^ l) :
    IsValidDecomposition (baseGadget params B l) (baseDecomp params B l) := by
  haveI : NeZero params.q := ⟨ne_of_gt params.q_pos.out⟩
  intro x
  dsimp [baseGadget, baseDecomp]
  have h_lt : ZMod.val x < B ^ l := lt_of_lt_of_le (ZMod.val_lt x) hq
  have h_nat := nat_base_decomp_sum B l (ZMod.val x) h_lt
  have h_cast :
      (∑ i : Fin l, ((((ZMod.val x / B ^ (i : ℕ)) % B : ℕ) : Zq params) *
        ((B ^ (i : ℕ) : ℕ) : Zq params))) =
      (((∑ i : Fin l, ((ZMod.val x / B ^ (i : ℕ)) % B) * B ^ (i : ℕ)) : ℕ) : Zq params) := by
    push_cast
    rfl
  rw [h_cast, h_nat, ZMod.natCast_zmod_val]

theorem baseDecomp_norm_lt (B l : ℕ) (hB : 0 < B) (h2B : 2 * B ≤ params.q)
    (x : Zq params) (i : Fin l) :
    norm params (baseDecomp params B l x i) < B := by
  haveI : NeZero params.q := ⟨ne_of_gt params.q_pos.out⟩
  dsimp [baseDecomp]
  set d : ℕ := (ZMod.val x / B ^ (i : ℕ)) % B
  have hd_lt_B : d < B := Nat.mod_lt _ hB
  have hd_lt_q : d < params.q := by omega
  have h_val : ZMod.val (d : Zq params) = d := ZMod.val_natCast_of_lt hd_lt_q
  unfold norm centeredLift
  dsimp
  rw [h_val]
  split_ifs <;> omega

def polyBaseGadget (N B l : ℕ) : VectorR (VectorR (Zq params) N) l :=
  fun j _ => baseGadget params B l j

def decomposePoly (N B l : ℕ) (p : VectorR (Zq params) N) : VectorR (VectorR (Zq params) N) l :=
  fun j k => baseDecomp params B l (p k) j

theorem decomposePoly_isValid (N B l : ℕ) (hq : params.q ≤ B ^ l) :
    IsValidDecomposition (polyBaseGadget params N B l) (decomposePoly params N B l) := by
  intro p
  ext k
  simp only [Finset.sum_apply, Pi.mul_apply, polyBaseGadget, decomposePoly]
  exact baseDecomp_isValid params B l hq (p k)

theorem decomposePoly_normInf_le (N B l : ℕ) (hB : 0 < B) (h2B : 2 * B ≤ params.q)
    (p : VectorR (Zq params) N) (j : Fin l) :
    normInf params (decomposePoly params N B l p j) ≤ B - 1 := by
  dsimp [normInf, decomposePoly]
  apply Finset.sup_le
  intro k _
  have h_lt := baseDecomp_norm_lt params B l hB h2B (p k) j
  omega

theorem concrete_gadgetRelinearize_correct (B l : ℕ) (hq : params.q ≤ B ^ l)
    (s d0 d1 d2 : Zq params) (a_rk e_rk : VectorR (Zq params) l) :
    let rk := mkGadgetRelinKey a_rk e_rk s (baseGadget params B l)
    let c_mul : RingSample2 (Zq params) := { d0 := d0, d1 := d1, d2 := d2 }
    let c_relin := gadgetRelinearize c_mul (baseDecomp params B l) rk
    c_relin.b - c_relin.a * s =
      (d0 - d1 * s + d2 * (s * s)) + (∑ i, baseDecomp params B l d2 i * e_rk i) :=
  gadgetRelinearize_correct s d0 d1 d2 a_rk e_rk (baseGadget params B l)
    (baseDecomp params B l) (baseDecomp_isValid params B l hq)

end ConcreteGadget

section NegacyclicPolyRing

open scoped BigOperators

@[ext]
structure NegacyclicPoly (R : Type*) (N : ℕ) where
  coeffs : Fin N → R

namespace NegacyclicPoly

variable {R : Type*} [CommRing R] {N : ℕ}

instance : Zero (NegacyclicPoly R N) := ⟨⟨fun _ => 0⟩⟩
instance : Add (NegacyclicPoly R N) := ⟨fun p q => ⟨fun k => p.coeffs k + q.coeffs k⟩⟩
instance : Neg (NegacyclicPoly R N) := ⟨fun p => ⟨fun k => -p.coeffs k⟩⟩
instance : Sub (NegacyclicPoly R N) := ⟨fun p q => ⟨fun k => p.coeffs k - q.coeffs k⟩⟩
instance : SMul ℕ (NegacyclicPoly R N) := ⟨fun n p => ⟨fun k => n • p.coeffs k⟩⟩
instance : SMul ℤ (NegacyclicPoly R N) := ⟨fun z p => ⟨fun k => z • p.coeffs k⟩⟩

@[simp] lemma zero_coeffs (k : Fin N) : (0 : NegacyclicPoly R N).coeffs k = 0 := rfl
@[simp] lemma add_coeffs (p q : NegacyclicPoly R N) (k : Fin N) :
    (p + q).coeffs k = p.coeffs k + q.coeffs k := rfl
@[simp] lemma neg_coeffs (p : NegacyclicPoly R N) (k : Fin N) :
    (-p).coeffs k = -p.coeffs k := rfl
@[simp] lemma sub_coeffs (p q : NegacyclicPoly R N) (k : Fin N) :
    (p - q).coeffs k = p.coeffs k - q.coeffs k := rfl

instance : AddCommGroup (NegacyclicPoly R N) where
  add_assoc a b c := by ext k; exact add_assoc _ _ _
  zero_add a := by ext k; exact zero_add _
  add_zero a := by ext k; exact add_zero _
  nsmul n a := n • a
  nsmul_zero a := by ext k; exact zero_nsmul _
  nsmul_succ n a := by ext k; exact succ_nsmul _ _
  zsmul z a := z • a
  zsmul_zero' a := by ext k; exact zero_zsmul _
  zsmul_succ' n a := by ext k; exact SubNegMonoid.zsmul_succ' n (a.coeffs k)
  zsmul_neg' n a := by ext k; exact SubNegMonoid.zsmul_neg' n (a.coeffs k)
  neg_add_cancel a := by ext k; exact neg_add_cancel _
  add_comm a b := by ext k; exact add_comm _ _
  sub_eq_add_neg a b := by ext k; exact sub_eq_add_neg _ _

@[simp] lemma sum_coeffs {ι : Type*} (s : Finset ι) (f : ι → NegacyclicPoly R N) (k : Fin N) :
    (∑ x ∈ s, f x).coeffs k = ∑ x ∈ s, (f x).coeffs k := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, add_coeffs, ih, Finset.sum_insert ha]

def negacyclicSign (N m : ℕ) : R :=
  (-1 : R) ^ (m / N)

def mulSchoolbook (p q : NegacyclicPoly R N) : NegacyclicPoly R N :=
  ⟨fun k =>
    ∑ i : Fin N, ∑ j : Fin N,
      if ((i : ℕ) + (j : ℕ)) % N = (k : ℕ) then
        negacyclicSign N ((i : ℕ) + (j : ℕ)) * p.coeffs i * q.coeffs j
      else 0⟩

instance : Mul (NegacyclicPoly R N) := ⟨mulSchoolbook⟩
instance : One (NegacyclicPoly R N) := ⟨⟨fun k => if (k : ℕ) = 0 then 1 else 0⟩⟩
instance : NatCast (NegacyclicPoly R N) := ⟨fun n => ⟨fun k => if (k : ℕ) = 0 then (n : R) else 0⟩⟩
instance : IntCast (NegacyclicPoly R N) := ⟨fun z => ⟨fun k => if (k : ℕ) = 0 then (z : R) else 0⟩⟩

@[simp] lemma one_coeffs (k : Fin N) :
    (1 : NegacyclicPoly R N).coeffs k = if (k : ℕ) = 0 then 1 else 0 := rfl

@[simp] lemma mul_coeffs (p q : NegacyclicPoly R N) (k : Fin N) :
    (p * q).coeffs k =
      ∑ i : Fin N, ∑ j : Fin N,
        if ((i : ℕ) + (j : ℕ)) % N = (k : ℕ) then
          negacyclicSign N ((i : ℕ) + (j : ℕ)) * p.coeffs i * q.coeffs j
        else 0 := rfl

theorem mul_coeffs_eq_schoolbook_branches (p q : NegacyclicPoly R N) (k : Fin N) :
    (p * q).coeffs k =
      ∑ i : Fin N, ∑ j : Fin N,
        if (i : ℕ) + (j : ℕ) < N then
          if (i : ℕ) + (j : ℕ) = (k : ℕ) then p.coeffs i * q.coeffs j else 0
        else
          if (i : ℕ) + (j : ℕ) - N = (k : ℕ) then -(p.coeffs i * q.coeffs j) else 0 := by
  rw [mul_coeffs]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hi := i.isLt
  have hj := j.isLt
  by_cases hlt : (i : ℕ) + (j : ℕ) < N
  · rw [if_pos hlt]
    have hmod : ((i : ℕ) + (j : ℕ)) % N = (i : ℕ) + (j : ℕ) := Nat.mod_eq_of_lt hlt
    have hdiv : ((i : ℕ) + (j : ℕ)) / N = 0 := Nat.div_eq_of_lt hlt
    simp [negacyclicSign, hmod, hdiv]
  · rw [if_neg hlt]
    have hge : N ≤ (i : ℕ) + (j : ℕ) := by omega
    have hsub_lt : (i : ℕ) + (j : ℕ) - N < N := by omega
    have hmod : ((i : ℕ) + (j : ℕ)) % N = (i : ℕ) + (j : ℕ) - N := by
      rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hsub_lt]
    have hdiv : ((i : ℕ) + (j : ℕ)) / N = 1 := by
      have h_eq : (i : ℕ) + (j : ℕ) = ((i : ℕ) + (j : ℕ) - N) + N * 1 := by omega
      have hN_pos : 0 < N := by omega
      rw [h_eq, Nat.add_mul_div_left _ _ hN_pos, Nat.div_eq_of_lt hsub_lt]
    simp [negacyclicSign, hmod, hdiv]

lemma div_add_mod_div (a b N : ℕ) (hN : 0 < N) :
    a / N + (a % N + b) / N = (a + b) / N := by
  have h1 : a + b = (a % N + b) + N * (a / N) := by
    have h_div := Nat.div_add_mod a N
    omega
  rw [h1, Nat.add_mul_div_left (a % N + b) (a / N) hN]
  omega

lemma negacyclicSign_mul_mod_left (a b N : ℕ) (hN : 0 < N) :
    (negacyclicSign N (a % N + b) : R) * negacyclicSign N a = negacyclicSign N (a + b) := by
  unfold negacyclicSign
  rw [← pow_add, add_comm ((a % N + b) / N) (a / N), div_add_mod_div a b N hN]

lemma negacyclicSign_mul_mod_right (a b N : ℕ) (hN : 0 < N) :
    (negacyclicSign N (a + b % N) : R) * negacyclicSign N b = negacyclicSign N (a + b) := by
  have h_comm1 : a + b % N = b % N + a := Nat.add_comm a (b % N)
  have h_comm2 : a + b = b + a := Nat.add_comm a b
  rw [h_comm1, h_comm2]
  exact negacyclicSign_mul_mod_left b a N hN

lemma mul_assoc_eq_triple_sum [hN : Fact (0 < N)]
    (p q r : NegacyclicPoly R N) (k : Fin N) :
    ((p * q) * r).coeffs k =
      ∑ i : Fin N, ∑ j : Fin N, ∑ l : Fin N,
        if ((i : ℕ) + (j : ℕ) + (l : ℕ)) % N = (k : ℕ) then
          negacyclicSign N ((i : ℕ) + (j : ℕ) + (l : ℕ)) * p.coeffs i * q.coeffs j * r.coeffs l
        else 0 := by
  simp only [mul_coeffs]
  have h_step1 :
      (∑ u : Fin N, ∑ l : Fin N,
        if ((u : ℕ) + (l : ℕ)) % N = (k : ℕ) then
          negacyclicSign N ((u : ℕ) + (l : ℕ)) *
            (∑ i : Fin N, ∑ j : Fin N,
              if ((i : ℕ) + (j : ℕ)) % N = (u : ℕ) then
                negacyclicSign N ((i : ℕ) + (j : ℕ)) * p.coeffs i * q.coeffs j
              else 0) * r.coeffs l
        else 0) =
      ∑ u : Fin N, ∑ l : Fin N, ∑ i : Fin N, ∑ j : Fin N,
        if ((u : ℕ) + (l : ℕ)) % N = (k : ℕ) then
          if ((i : ℕ) + (j : ℕ)) % N = (u : ℕ) then
            negacyclicSign N ((u : ℕ) + (l : ℕ)) *
              (negacyclicSign N ((i : ℕ) + (j : ℕ)) * p.coeffs i * q.coeffs j) * r.coeffs l
          else 0
        else 0 := by
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro l _
    by_cases hul : ((u : ℕ) + (l : ℕ)) % N = (k : ℕ)
    · simp only [if_pos hul, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      split_ifs <;> ring
    · simp [if_neg hul]
  rw [h_step1]
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
  conv_lhs =>
    arg 2; ext l
    rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
    arg 2; ext i
    rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
  conv_lhs =>
    arg 2; ext i
    rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro l _
  let u0 : Fin N := ⟨((i : ℕ) + (j : ℕ)) % N, Nat.mod_lt _ hN.out⟩
  have h_inner :
      (∑ u : Fin N,
        if ((u : ℕ) + (l : ℕ)) % N = (k : ℕ) then
          if ((i : ℕ) + (j : ℕ)) % N = (u : ℕ) then
            negacyclicSign N ((u : ℕ) + (l : ℕ)) *
              (negacyclicSign N ((i : ℕ) + (j : ℕ)) * p.coeffs i * q.coeffs j) * r.coeffs l
          else 0
        else 0) =
      if ((u0 : ℕ) + (l : ℕ)) % N = (k : ℕ) then
        negacyclicSign N ((u0 : ℕ) + (l : ℕ)) *
          (negacyclicSign N ((i : ℕ) + (j : ℕ)) * p.coeffs i * q.coeffs j) * r.coeffs l
      else 0 := by
    have h_eq : ∀ u : Fin N, (((i : ℕ) + (j : ℕ)) % N = (u : ℕ)) ↔ u = u0 := by
      intro u
      rw [Fin.ext_iff, eq_comm]
    simp_rw [h_eq]
    have h_ite : ∀ u : Fin N,
        (if ((u : ℕ) + (l : ℕ)) % N = (k : ℕ) then
          if u = u0 then
            negacyclicSign N ((u : ℕ) + (l : ℕ)) *
              (negacyclicSign N ((i : ℕ) + (j : ℕ)) * p.coeffs i * q.coeffs j) * r.coeffs l
          else 0
        else 0) =
        if u = u0 then
          if ((u0 : ℕ) + (l : ℕ)) % N = (k : ℕ) then
            negacyclicSign N ((u0 : ℕ) + (l : ℕ)) *
              (negacyclicSign N ((i : ℕ) + (j : ℕ)) * p.coeffs i * q.coeffs j) * r.coeffs l
          else 0
        else 0 := by
      intro u
      by_cases hu : u = u0
      · subst hu; simp
      · simp [hu]
    simp_rw [h_ite]
    simp
  rw [h_inner]
  have hu0_mod : ((u0 : ℕ) + (l : ℕ)) % N = ((i : ℕ) + (j : ℕ) + (l : ℕ)) % N := by
    change (((i : ℕ) + (j : ℕ)) % N + (l : ℕ)) % N = ((i : ℕ) + (j : ℕ) + (l : ℕ)) % N
    exact Nat.mod_add_mod ((i : ℕ) + (j : ℕ)) N (l : ℕ)
  have hu0_sign :
      (negacyclicSign N ((u0 : ℕ) + (l : ℕ)) : R) * negacyclicSign N ((i : ℕ) + (j : ℕ)) =
      negacyclicSign N ((i : ℕ) + (j : ℕ) + (l : ℕ)) := by
    change (negacyclicSign N (((i : ℕ) + (j : ℕ)) % N + (l : ℕ)) : R) *
      negacyclicSign N ((i : ℕ) + (j : ℕ)) = _
    exact negacyclicSign_mul_mod_left ((i : ℕ) + (j : ℕ)) (l : ℕ) N hN.out
  rw [hu0_mod]
  split_ifs with hmod
  · calc
      negacyclicSign N ((u0 : ℕ) + (l : ℕ)) *
          (negacyclicSign N ((i : ℕ) + (j : ℕ)) * p.coeffs i * q.coeffs j) * r.coeffs l
        = (negacyclicSign N ((u0 : ℕ) + (l : ℕ)) * negacyclicSign N ((i : ℕ) + (j : ℕ))) *
            p.coeffs i * q.coeffs j * r.coeffs l := by ring
      _ = negacyclicSign N ((i : ℕ) + (j : ℕ) + (l : ℕ)) *
            p.coeffs i * q.coeffs j * r.coeffs l := by
        rw [hu0_sign]
  · rfl

lemma mul_comm_poly (p q : NegacyclicPoly R N) : p * q = q * p := by
  ext k
  simp only [mul_coeffs]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  have h_add : (i : ℕ) + (j : ℕ) = (j : ℕ) + (i : ℕ) := Nat.add_comm _ _
  rw [h_add]
  split_ifs <;> ring

lemma left_distrib_poly (p q r : NegacyclicPoly R N) : p * (q + r) = p * q + p * r := by
  ext k
  simp only [mul_coeffs, add_coeffs]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> ring

lemma right_distrib_poly (p q r : NegacyclicPoly R N) : (p + q) * r = p * r + q * r := by
  rw [mul_comm_poly (p + q) r, left_distrib_poly, mul_comm_poly p r, mul_comm_poly q r]

lemma zero_mul_poly (p : NegacyclicPoly R N) : 0 * p = 0 := by
  ext k
  simp [mul_coeffs]

lemma mul_zero_poly (p : NegacyclicPoly R N) : p * 0 = 0 := by
  ext k
  simp [mul_coeffs]

lemma one_mul_poly [hN : Fact (0 < N)] (p : NegacyclicPoly R N) : 1 * p = p := by
  ext k
  simp only [mul_coeffs, one_coeffs]
  let z0 : Fin N := ⟨0, hN.out⟩
  have hz0 : ∀ i : Fin N, ((i : ℕ) = 0) ↔ i = z0 := by
    intro i
    rw [Fin.ext_iff]
  simp_rw [hz0]
  have h_outer :
      (∑ i : Fin N, ∑ j : Fin N,
        if ((i : ℕ) + (j : ℕ)) % N = (k : ℕ) then
          negacyclicSign N ((i : ℕ) + (j : ℕ)) * (if i = z0 then (1 : R) else 0) * p.coeffs j
        else 0) =
      ∑ j : Fin N,
        if ((z0 : ℕ) + (j : ℕ)) % N = (k : ℕ) then
          negacyclicSign N ((z0 : ℕ) + (j : ℕ)) * 1 * p.coeffs j
        else 0 := by
    have h_ite : ∀ i : Fin N,
        (∑ j : Fin N,
          if ((i : ℕ) + (j : ℕ)) % N = (k : ℕ) then
            negacyclicSign N ((i : ℕ) + (j : ℕ)) * (if i = z0 then (1 : R) else 0) * p.coeffs j
          else 0) =
        if i = z0 then
          ∑ j : Fin N,
            if ((z0 : ℕ) + (j : ℕ)) % N = (k : ℕ) then
              negacyclicSign N ((z0 : ℕ) + (j : ℕ)) * 1 * p.coeffs j
            else 0
        else 0 := by
      intro i
      by_cases hi : i = z0
      · subst hi; simp
      · simp [hi]
    simp_rw [h_ite]
    simp
  rw [h_outer]
  have h_inner :
      (∑ j : Fin N,
        if ((z0 : ℕ) + (j : ℕ)) % N = (k : ℕ) then
          negacyclicSign N ((z0 : ℕ) + (j : ℕ)) * 1 * p.coeffs j
        else 0) =
      ∑ j : Fin N, if j = k then p.coeffs j else 0 := by
    apply Finset.sum_congr rfl
    intro j _
    have hj_mod : ((z0 : ℕ) + (j : ℕ)) % N = (j : ℕ) := by
      change (0 + (j : ℕ)) % N = (j : ℕ)
      rw [Nat.zero_add, Nat.mod_eq_of_lt j.isLt]
    have hj_sign : (negacyclicSign N ((z0 : ℕ) + (j : ℕ)) : R) = 1 := by
      unfold negacyclicSign
      change (-1 : R) ^ ((0 + (j : ℕ)) / N) = 1
      rw [Nat.zero_add, Nat.div_eq_of_lt j.isLt, pow_zero]
    rw [hj_mod, hj_sign]
    simp [Fin.ext_iff]
  rw [h_inner]
  simp

lemma mul_one_poly [Fact (0 < N)] (p : NegacyclicPoly R N) : p * 1 = p := by
  rw [mul_comm_poly, one_mul_poly]

lemma mul_assoc_poly [Fact (0 < N)] (p q r : NegacyclicPoly R N) :
    (p * q) * r = p * (q * r) := by
  ext k
  have h_lhs := mul_assoc_eq_triple_sum p q r k
  have h_rhs : (p * (q * r)).coeffs k = ((q * r) * p).coeffs k := by
    rw [mul_comm_poly p (q * r)]
  rw [h_lhs, h_rhs, mul_assoc_eq_triple_sum q r p k]
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
  conv_rhs =>
    arg 2; ext l
    rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro l _
  have h_add : (j : ℕ) + (i : ℕ) + (l : ℕ) = (i : ℕ) + (l : ℕ) + (j : ℕ) := by omega
  rw [h_add]
  split_ifs <;> ring

instance [Fact (0 < N)] : CommRing (NegacyclicPoly R N) where
  mul := (· * ·)
  mul_assoc := mul_assoc_poly
  one := 1
  one_mul := one_mul_poly
  mul_one := mul_one_poly
  zero_mul := zero_mul_poly
  mul_zero := mul_zero_poly
  left_distrib := left_distrib_poly
  right_distrib := right_distrib_poly
  mul_comm := mul_comm_poly
  natCast n := (n : NegacyclicPoly R N)
  natCast_zero := by
    ext k
    change (if (k : ℕ) = 0 then ((0 : ℕ) : R) else 0) = 0
    simp
  natCast_succ n := by
    ext k
    change (if (k : ℕ) = 0 then ((n + 1 : ℕ) : R) else 0) =
      (if (k : ℕ) = 0 then (n : R) else 0) + (if (k : ℕ) = 0 then 1 else 0)
    split_ifs <;> simp
  intCast z := (z : NegacyclicPoly R N)
  intCast_ofNat n := by
    ext k
    change (if (k : ℕ) = 0 then ((n : ℤ) : R) else 0) = if (k : ℕ) = 0 then (n : R) else 0
    split_ifs <;> simp
  intCast_negSucc n := by
    ext k
    change (if (k : ℕ) = 0 then (Int.negSucc n : R) else 0) =
      -(if (k : ℕ) = 0 then ((n + 1 : ℕ) : R) else 0)
    split_ifs <;> simp [Int.negSucc_eq]

def constPoly (c : R) : NegacyclicPoly R N :=
  ⟨fun k => if (k : ℕ) = 0 then c else 0⟩

theorem constPoly_mul_coeffs [hN : Fact (0 < N)] (c : R) (p : NegacyclicPoly R N) (k : Fin N) :
    (constPoly c * p).coeffs k = c * p.coeffs k := by
  simp only [mul_coeffs, constPoly]
  let z0 : Fin N := ⟨0, hN.out⟩
  have hz0 : ∀ i : Fin N, ((i : ℕ) = 0) ↔ i = z0 := by
    intro i; rw [Fin.ext_iff]
  simp_rw [hz0]
  have h_outer :
      (∑ i : Fin N, ∑ j : Fin N,
        if ((i : ℕ) + (j : ℕ)) % N = (k : ℕ) then
          negacyclicSign N ((i : ℕ) + (j : ℕ)) * (if i = z0 then c else 0) * p.coeffs j
        else 0) =
      ∑ j : Fin N,
        if ((z0 : ℕ) + (j : ℕ)) % N = (k : ℕ) then
          negacyclicSign N ((z0 : ℕ) + (j : ℕ)) * c * p.coeffs j
        else 0 := by
    have h_ite : ∀ i : Fin N,
        (∑ j : Fin N,
          if ((i : ℕ) + (j : ℕ)) % N = (k : ℕ) then
            negacyclicSign N ((i : ℕ) + (j : ℕ)) * (if i = z0 then c else 0) * p.coeffs j
          else 0) =
        if i = z0 then
          ∑ j : Fin N,
            if ((z0 : ℕ) + (j : ℕ)) % N = (k : ℕ) then
              negacyclicSign N ((z0 : ℕ) + (j : ℕ)) * c * p.coeffs j
            else 0
        else 0 := by
      intro i
      by_cases hi : i = z0
      · subst hi; simp
      · simp [hi]
    simp_rw [h_ite]
    simp
  rw [h_outer]
  have h_inner :
      (∑ j : Fin N,
        if ((z0 : ℕ) + (j : ℕ)) % N = (k : ℕ) then
          negacyclicSign N ((z0 : ℕ) + (j : ℕ)) * c * p.coeffs j
        else 0) =
      ∑ j : Fin N, if j = k then c * p.coeffs j else 0 := by
    apply Finset.sum_congr rfl
    intro j _
    have hj_mod : ((z0 : ℕ) + (j : ℕ)) % N = (j : ℕ) := by
      change (0 + (j : ℕ)) % N = (j : ℕ)
      rw [Nat.zero_add, Nat.mod_eq_of_lt j.isLt]
    have hj_sign : (negacyclicSign N ((z0 : ℕ) + (j : ℕ)) : R) = 1 := by
      unfold negacyclicSign
      change (-1 : R) ^ ((0 + (j : ℕ)) / N) = 1
      rw [Nat.zero_add, Nat.div_eq_of_lt j.isLt, pow_zero]
    rw [hj_mod, hj_sign]
    simp [Fin.ext_iff]
  rw [h_inner]
  simp

def negacyclicGadget (params : LWEParams) (N B l : ℕ) :
    VectorR (NegacyclicPoly (Zq params) N) l :=
  fun i => constPoly (baseGadget params B l i)

def negacyclicDecomp (params : LWEParams) (N B l : ℕ)
    (p : NegacyclicPoly (Zq params) N) : VectorR (NegacyclicPoly (Zq params) N) l :=
  fun i => ⟨fun k => baseDecomp params B l (p.coeffs k) i⟩

theorem negacyclicDecomp_isValid (params : LWEParams) (N B l : ℕ) [Fact (0 < N)]
    (hq : params.q ≤ B ^ l) :
    IsValidDecomposition (negacyclicGadget params N B l) (negacyclicDecomp params N B l) := by
  intro p
  ext k
  rw [sum_coeffs]
  have h_comm : ∀ i : Fin l,
      (negacyclicDecomp params N B l p i * negacyclicGadget params N B l i).coeffs k =
      baseDecomp params B l (p.coeffs k) i * baseGadget params B l i := by
    intro i
    rw [mul_comm (negacyclicDecomp params N B l p i) (negacyclicGadget params N B l i)]
    change (constPoly (baseGadget params B l i) * negacyclicDecomp params N B l p i).coeffs k = _
    rw [constPoly_mul_coeffs, mul_comm]
    rfl
  simp_rw [h_comm]
  exact baseDecomp_isValid params B l hq (p.coeffs k)

theorem negacyclic_poly_mul_and_gadgetRelinearize_correct
    (params : LWEParams) (N B l : ℕ) [Fact (0 < N)] (hq : params.q ≤ B ^ l)
    (s a1 a2 e1 e2 : NegacyclicPoly (Zq params) N)
    (a_rk e_rk : VectorR (NegacyclicPoly (Zq params) N) l) :
    let c1 := mkRingSample a1 s e1
    let c2 := mkRingSample a2 s e2
    let c_mul := mulRingSamples c1 c2
    let rk := mkGadgetRelinKey a_rk e_rk s (negacyclicGadget params N B l)
    let c_relin := gadgetRelinearize c_mul (negacyclicDecomp params N B l) rk
    c_relin.b - c_relin.a * s =
      e1 * e2 + (∑ i : Fin l, negacyclicDecomp params N B l c_mul.d2 i * e_rk i) := by
  intro c1 c2 c_mul rk c_relin
  have h_relin := gadgetRelinearize_correct s c_mul.d0 c_mul.d1 c_mul.d2 a_rk e_rk
    (negacyclicGadget params N B l) (negacyclicDecomp params N B l)
    (negacyclicDecomp_isValid params N B l hq)
  have h_mul := mulRingSamples_correct s a1 a2 e1 e2
  dsimp at h_relin h_mul
  rw [h_relin, h_mul]

def IsTernaryPoly {R : Type*} [Ring R] {N : ℕ} (c : NegacyclicPoly R N) : Prop :=
  ∀ i : Fin N, IsTernaryElem (c.coeffs i)

lemma norm_neg_one_pow_mul (params : LWEParams) (x : Zq params) :
    ∀ d : ℕ, norm params ((-1 : Zq params) ^ d * x) = norm params x
  | 0 => by simp
  | d + 1 => by
    rw [pow_succ', neg_one_mul, neg_mul, norm_neg_elem, norm_neg_one_pow_mul params x d]

lemma norm_negacyclicSign_mul (params : LWEParams) (N m : ℕ) (x : Zq params) :
    norm params (negacyclicSign N m * x) = norm params x :=
  norm_neg_one_pow_mul params x (m / N)

lemma mod_add_eq_iff_fin [hN : Fact (0 < N)] (i k j : Fin N) :
    (((i : ℕ) + (j : ℕ)) % N = (k : ℕ)) ↔
      j = ⟨((k : ℕ) + N - (i : ℕ)) % N, Nat.mod_lt _ hN.out⟩ := by
  have hi := i.isLt
  have hk := k.isLt
  have hj := j.isLt
  rw [Fin.ext_iff]
  dsimp
  by_cases hik : (i : ℕ) ≤ (k : ℕ)
  · have h_rhs : ((k : ℕ) + N - (i : ℕ)) % N = (k : ℕ) - (i : ℕ) := by
      have h_eq : (k : ℕ) + N - (i : ℕ) = ((k : ℕ) - (i : ℕ)) + N * 1 := by omega
      have h_lt : (k : ℕ) - (i : ℕ) < N := by omega
      rw [h_eq, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h_lt]
    rw [h_rhs]
    by_cases hlt : (i : ℕ) + (j : ℕ) < N
    · rw [Nat.mod_eq_of_lt hlt]
      omega
    · have hge : N ≤ (i : ℕ) + (j : ℕ) := by omega
      have hsub : (i : ℕ) + (j : ℕ) - N < N := by omega
      rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hsub]
      omega
  · have h_rhs : ((k : ℕ) + N - (i : ℕ)) % N = (k : ℕ) + N - (i : ℕ) := by
      have h_lt : (k : ℕ) + N - (i : ℕ) < N := by omega
      exact Nat.mod_eq_of_lt h_lt
    rw [h_rhs]
    by_cases hlt : (i : ℕ) + (j : ℕ) < N
    · rw [Nat.mod_eq_of_lt hlt]
      omega
    · have hge : N ≤ (i : ℕ) + (j : ℕ) := by omega
      have hsub : (i : ℕ) + (j : ℕ) - N < N := by omega
      rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hsub]
      omega

theorem normInf_ternary_mul_le (params : LWEParams) (N : ℕ) [hN : Fact (0 < N)]
    (c s : NegacyclicPoly (Zq params) N) (hc : IsTernaryPoly c) :
    normInf params (c * s).coeffs ≤ N * normInf params s.coeffs := by
  dsimp [normInf]
  apply Finset.sup_le
  intro k _
  have h_sum_le := norm_finset_sum_le params Finset.univ (fun i : Fin N =>
    ∑ j : Fin N,
      if ((i : ℕ) + (j : ℕ)) % N = (k : ℕ) then
        negacyclicSign N ((i : ℕ) + (j : ℕ)) * c.coeffs i * s.coeffs j
      else 0)
  have h_term_le :
      (∑ i : Fin N, norm params (
        ∑ j : Fin N,
          if ((i : ℕ) + (j : ℕ)) % N = (k : ℕ) then
            negacyclicSign N ((i : ℕ) + (j : ℕ)) * c.coeffs i * s.coeffs j
          else 0)) ≤
      ∑ _i : Fin N, Finset.univ.sup (fun j => norm params (s.coeffs j)) := by
    apply Finset.sum_le_sum
    intro i _
    let j0 : Fin N := ⟨((k : ℕ) + N - (i : ℕ)) % N, Nat.mod_lt _ hN.out⟩
    have hj0 : ∀ j : Fin N, (((i : ℕ) + (j : ℕ)) % N = (k : ℕ)) ↔ j = j0 :=
      mod_add_eq_iff_fin i k
    simp_rw [hj0]
    have h_inner :
        (∑ j : Fin N,
          if j = j0 then
            negacyclicSign N ((i : ℕ) + (j : ℕ)) * c.coeffs i * s.coeffs j
          else 0) =
        negacyclicSign N ((i : ℕ) + (j0 : ℕ)) * (c.coeffs i * s.coeffs j0) := by
      simp [mul_assoc]
    rw [h_inner, norm_negacyclicSign_mul]
    have h1 := norm_ternary_mul_le params (c.coeffs i) (s.coeffs j0) (hc i)
    have h2 : norm params (s.coeffs j0) ≤ Finset.univ.sup (fun j => norm params (s.coeffs j)) :=
      Finset.le_sup (f := fun j => norm params (s.coeffs j)) (Finset.mem_univ j0)
    omega
  have h_const :
      (∑ _i : Fin N, Finset.univ.sup (fun j => norm params (s.coeffs j))) =
        N * Finset.univ.sup (fun j => norm params (s.coeffs j)) := by
    simp
  omega

end NegacyclicPoly

end NegacyclicPolyRing

section NTT

variable (PolyR : Type*) [CommRing PolyR]
variable (ScalarR : Type*) [CommRing ScalarR]
variable (N : ℕ)

structure NTTHom (PolyR : Type*) [CommRing PolyR] (N : ℕ) (ScalarR : Type*) [CommRing ScalarR] where
  toFun : PolyR → (Fin N → ScalarR)
  map_add : ∀ x y : PolyR, toFun (x + y) = toFun x + toFun y
  map_mul : ∀ x y : PolyR, toFun (x * y) = toFun x * toFun y
  map_sum : ∀ {ι : Type} (s : Finset ι) (f : ι → PolyR), toFun (∑ x ∈ s, f x) = ∑ x ∈ s, toFun (f x)

structure NTTSample where
  a_ntt : Fin N → ScalarR
  b_ntt : Fin N → ScalarR

def toNTT (c : RingSample PolyR) (ntt : NTTHom PolyR N ScalarR) : NTTSample ScalarR N :=
  { a_ntt := ntt.toFun c.a,
    b_ntt := ntt.toFun c.b }

structure NTTSample2 where
  d0_ntt : Fin N → ScalarR
  d1_ntt : Fin N → ScalarR
  d2_ntt : Fin N → ScalarR

def nttMultiply (x y : NTTSample ScalarR N) : NTTSample2 ScalarR N :=
  { d0_ntt := x.b_ntt * y.b_ntt,
    d1_ntt := x.a_ntt * y.b_ntt + x.b_ntt * y.a_ntt,
    d2_ntt := x.a_ntt * y.a_ntt }

theorem ntt_multiply_correct (c1 c2 : RingSample PolyR) (ntt : NTTHom PolyR N ScalarR) :
    let c_mul := mulRingSamples c1 c2
    let ntt_c_mul : NTTSample2 ScalarR N :=
      { d0_ntt := ntt.toFun c_mul.d0, d1_ntt := ntt.toFun c_mul.d1, d2_ntt := ntt.toFun c_mul.d2 }
    let ntt1 := toNTT PolyR ScalarR N c1 ntt
    let ntt2 := toNTT PolyR ScalarR N c2 ntt
    nttMultiply ScalarR N ntt1 ntt2 = ntt_c_mul := by
  dsimp [mulRingSamples, toNTT, nttMultiply]
  congr
  · exact (ntt.map_mul c1.b c2.b).symm
  · rw [ntt.map_add, ntt.map_mul, ntt.map_mul]
    ring
  · exact (ntt.map_mul c1.a c2.a).symm

end NTT

section ConcreteNTT

open scoped BigOperators

variable {R : Type*} [CommRing R] {N : ℕ}

def oddRoot (ψ : R) (m : Fin N) : R :=
  ψ ^ (2 * (m : ℕ) + 1)

def concreteNTT (ψ : R) (p : NegacyclicPoly R N) : Fin N → R :=
  fun m => ∑ j : Fin N, p.coeffs j * (oddRoot ψ m) ^ (j : ℕ)

def concreteInvNTT (ψ_inv n_inv : R) (evals : Fin N → R) : NegacyclicPoly R N :=
  ⟨fun i => n_inv * ∑ m : Fin N, evals m * ψ_inv ^ ((2 * (m : ℕ) + 1) * (i : ℕ))⟩

lemma oddRoot_pow_N (ψ : R) (hpsi : ψ ^ N = -1) (m : Fin N) :
    (oddRoot ψ m) ^ N = -1 := by
  unfold oddRoot
  rw [← pow_mul, mul_comm (2 * (m : ℕ) + 1) N, pow_mul, hpsi]
  rw [pow_add, pow_mul, pow_one]
  have h2 : (-1 : R) ^ 2 = 1 := by ring
  rw [h2, one_pow, one_mul]

lemma oddRoot_pow_eq_negacyclicSign (ψ : R) (hpsi : ψ ^ N = -1) (m : Fin N) (a : ℕ) :
    (oddRoot ψ m) ^ a = NegacyclicPoly.negacyclicSign N a * (oddRoot ψ m) ^ (a % N) := by
  have h_div : a = N * (a / N) + a % N := (Nat.div_add_mod a N).symm
  conv_lhs => rw [h_div]
  rw [pow_add, pow_mul, oddRoot_pow_N ψ hpsi m]
  rfl

theorem concreteNTT_map_add (ψ : R) (p q : NegacyclicPoly R N) :
    concreteNTT ψ (p + q) = concreteNTT ψ p + concreteNTT ψ q := by
  ext m
  simp only [concreteNTT, Pi.add_apply, NegacyclicPoly.add_coeffs, add_mul, Finset.sum_add_distrib]

theorem concreteNTT_map_sum (ψ : R) {ι : Type} (s : Finset ι) (f : ι → NegacyclicPoly R N) :
    concreteNTT ψ (∑ x ∈ s, f x) = ∑ x ∈ s, concreteNTT ψ (f x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    ext m
    simp [concreteNTT]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, concreteNTT_map_add, ih, Finset.sum_insert ha]

theorem concreteNTT_map_mul [hN : Fact (0 < N)] (ψ : R) (hpsi : ψ ^ N = -1)
    (p q : NegacyclicPoly R N) :
    concreteNTT ψ (p * q) = concreteNTT ψ p * concreteNTT ψ q := by
  ext m
  simp only [concreteNTT, Pi.mul_apply, NegacyclicPoly.mul_coeffs]
  have h_push :
      (∑ k : Fin N,
        (∑ i : Fin N, ∑ j : Fin N,
          if ((i : ℕ) + (j : ℕ)) % N = (k : ℕ) then
            NegacyclicPoly.negacyclicSign N ((i : ℕ) + (j : ℕ)) * p.coeffs i * q.coeffs j
          else 0) * (oddRoot ψ m) ^ (k : ℕ)) =
      ∑ k : Fin N, ∑ i : Fin N, ∑ j : Fin N,
        if ((i : ℕ) + (j : ℕ)) % N = (k : ℕ) then
          NegacyclicPoly.negacyclicSign N ((i : ℕ) + (j : ℕ)) * p.coeffs i * q.coeffs j *
            (oddRoot ψ m) ^ (k : ℕ)
        else 0 := by
    apply Finset.sum_congr rfl
    intro k _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> ring
  rw [h_push]
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
  conv_lhs =>
    arg 2; ext i
    rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)]
  have h_collapse :
      (∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N,
        if ((i : ℕ) + (j : ℕ)) % N = (k : ℕ) then
          NegacyclicPoly.negacyclicSign N ((i : ℕ) + (j : ℕ)) * p.coeffs i * q.coeffs j *
            (oddRoot ψ m) ^ (k : ℕ)
        else 0) =
      ∑ i : Fin N, ∑ j : Fin N,
        (p.coeffs i * (oddRoot ψ m) ^ (i : ℕ)) * (q.coeffs j * (oddRoot ψ m) ^ (j : ℕ)) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    let k0 : Fin N := ⟨((i : ℕ) + (j : ℕ)) % N, Nat.mod_lt _ hN.out⟩
    have hk0 : ∀ k : Fin N, (((i : ℕ) + (j : ℕ)) % N = (k : ℕ)) ↔ k = k0 := by
      intro k
      rw [Fin.ext_iff, eq_comm]
    simp_rw [hk0]
    have h_sum_k :
        (∑ k : Fin N,
          if k = k0 then
            NegacyclicPoly.negacyclicSign N ((i : ℕ) + (j : ℕ)) * p.coeffs i * q.coeffs j *
              (oddRoot ψ m) ^ (k : ℕ)
          else 0) =
        NegacyclicPoly.negacyclicSign N ((i : ℕ) + (j : ℕ)) * p.coeffs i * q.coeffs j *
          (oddRoot ψ m) ^ (((i : ℕ) + (j : ℕ)) % N) := by
      simp [k0]
    rw [h_sum_k]
    have h_pow := oddRoot_pow_eq_negacyclicSign ψ hpsi m ((i : ℕ) + (j : ℕ))
    calc
      NegacyclicPoly.negacyclicSign N ((i : ℕ) + (j : ℕ)) * p.coeffs i * q.coeffs j *
          (oddRoot ψ m) ^ (((i : ℕ) + (j : ℕ)) % N)
        = p.coeffs i * q.coeffs j *
            (NegacyclicPoly.negacyclicSign N ((i : ℕ) + (j : ℕ)) *
              (oddRoot ψ m) ^ (((i : ℕ) + (j : ℕ)) % N)) := by ring
      _ = p.coeffs i * q.coeffs j * (oddRoot ψ m) ^ ((i : ℕ) + (j : ℕ)) := by rw [← h_pow]
      _ = (p.coeffs i * (oddRoot ψ m) ^ (i : ℕ)) * (q.coeffs j * (oddRoot ψ m) ^ (j : ℕ)) := by
        rw [pow_add]
        ring
  rw [h_collapse, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.mul_sum]

def concreteNTTHom [Fact (0 < N)] (ψ : R) (hpsi : ψ ^ N = -1) :
    NTTHom (NegacyclicPoly R N) N R where
  toFun := concreteNTT ψ
  map_add := concreteNTT_map_add ψ
  map_mul := concreteNTT_map_mul ψ hpsi
  map_sum := concreteNTT_map_sum ψ

def IsValidNTTInverse (N : ℕ) (ψ ψ_inv n_inv : R) : Prop :=
  ∀ j i : Fin N,
    n_inv * (∑ m : Fin N, (oddRoot ψ m) ^ (j : ℕ) * ψ_inv ^ ((2 * (m : ℕ) + 1) * (i : ℕ))) =
      if j = i then 1 else 0

lemma oddRoot_mul_inv_diag (ψ ψ_inv : R) (h_inv : ψ * ψ_inv = 1) (m : Fin N) (i : ℕ) :
    (oddRoot ψ m) ^ i * ψ_inv ^ ((2 * (m : ℕ) + 1) * i) = 1 := by
  unfold oddRoot
  rw [← pow_mul, ← mul_pow, h_inv, one_pow]

lemma oddRoot_mul_inv_term (ψ ψ_inv : R) (m : Fin N) (j i : ℕ) :
    (oddRoot ψ m) ^ j * ψ_inv ^ ((2 * (m : ℕ) + 1) * i) =
      (ψ ^ j * ψ_inv ^ i) * (ψ ^ (2 * j) * ψ_inv ^ (2 * i)) ^ (m : ℕ) := by
  unfold oddRoot
  have h1 : (2 * (m : ℕ) + 1) * j = j + (2 * j) * (m : ℕ) := by ring
  have h2 : (2 * (m : ℕ) + 1) * i = i + (2 * i) * (m : ℕ) := by ring
  rw [← pow_mul, h1, h2, pow_add, pow_add, pow_mul, pow_mul, mul_pow]
  ring

lemma finset_geom_sum_mul (r : R) :
    ∀ n : ℕ, (∑ m ∈ Finset.range n, r ^ m) * (r - 1) = r ^ n - 1
  | 0 => by simp
  | n + 1 => by
    rw [Finset.sum_range_succ, add_mul, finset_geom_sum_mul r n, pow_succ]
    ring

lemma oddRoot_ratio_pow_N_eq_one (ψ ψ_inv : R) (hpsi : ψ ^ N = -1) (h_inv : ψ * ψ_inv = 1)
    (j i : ℕ) :
    (ψ ^ (2 * j) * ψ_inv ^ (2 * i)) ^ N = 1 := by
  have h_psi2N : (ψ ^ N) ^ 2 = 1 := by
    rw [hpsi]
    ring
  have h_invN : (ψ_inv ^ N) ^ 2 = 1 := by
    have h_prod : (ψ ^ N) ^ 2 * (ψ_inv ^ N) ^ 2 = 1 := by
      rw [← mul_pow, ← mul_pow, h_inv, one_pow, one_pow]
    rw [h_psi2N, one_mul] at h_prod
    exact h_prod
  have hj : (ψ ^ (2 * j)) ^ N = ((ψ ^ N) ^ 2) ^ j := by
    rw [← pow_mul, ← pow_mul, ← pow_mul]
    congr 1
    ring
  have hi : (ψ_inv ^ (2 * i)) ^ N = ((ψ_inv ^ N) ^ 2) ^ i := by
    rw [← pow_mul, ← pow_mul, ← pow_mul]
    congr 1
    ring
  rw [mul_pow, hj, hi, h_psi2N, h_invN, one_pow, one_pow, mul_one]

theorem isValidNTTInverse_of_primitive [NoZeroDivisors R] (ψ ψ_inv n_inv : R)
    (hpsi : ψ ^ N = -1) (h_inv : ψ * ψ_inv = 1) (hn : n_inv * (N : R) = 1)
    (h_prim : ∀ j i : Fin N, j ≠ i → ψ ^ (2 * (j : ℕ)) * ψ_inv ^ (2 * (i : ℕ)) ≠ 1) :
    IsValidNTTInverse N ψ ψ_inv n_inv := by
  intro j i
  by_cases hji : j = i
  · subst hji
    rw [if_pos rfl]
    have h_diag : (∑ m : Fin N, (oddRoot ψ m) ^ (j : ℕ) * ψ_inv ^ ((2 * (m : ℕ) + 1) * (j : ℕ))) =
        (N : R) := by
      simp_rw [oddRoot_mul_inv_diag ψ ψ_inv h_inv _ (j : ℕ)]
      simp
    rw [h_diag, hn]
  · rw [if_neg hji]
    set r : R := ψ ^ (2 * (j : ℕ)) * ψ_inv ^ (2 * (i : ℕ))
    have h_factor :
        (∑ m : Fin N, (oddRoot ψ m) ^ (j : ℕ) * ψ_inv ^ ((2 * (m : ℕ) + 1) * (i : ℕ))) =
          (ψ ^ (j : ℕ) * ψ_inv ^ (i : ℕ)) * (∑ m : Fin N, r ^ (m : ℕ)) := by
      simp_rw [oddRoot_mul_inv_term ψ ψ_inv _ (j : ℕ) (i : ℕ)]
      rw [← Finset.mul_sum]
    have h_fin_sum : (∑ m : Fin N, r ^ (m : ℕ)) = ∑ m ∈ Finset.range N, r ^ m := by
      rw [← Fin.sum_univ_eq_sum_range (fun m => r ^ m) N]
    have h_geom : (∑ m ∈ Finset.range N, r ^ m) * (r - 1) = 0 := by
      rw [finset_geom_sum_mul r N,
        oddRoot_ratio_pow_N_eq_one ψ ψ_inv hpsi h_inv (j : ℕ) (i : ℕ), sub_self]
    have hr_ne : r - 1 ≠ 0 := sub_ne_zero.mpr (h_prim j i hji)
    have h_sum_zero : (∑ m ∈ Finset.range N, r ^ m) = 0 := by
      rcases mul_eq_zero.mp h_geom with h0 | h1
      · exact h0
      · exact False.elim (hr_ne h1)
    rw [h_factor, h_fin_sum, h_sum_zero, mul_zero, mul_zero]

theorem concreteInvNTT_concreteNTT (ψ ψ_inv n_inv : R)
    (h_orth : IsValidNTTInverse N ψ ψ_inv n_inv) (p : NegacyclicPoly R N) :
    concreteInvNTT ψ_inv n_inv (concreteNTT ψ p) = p := by
  ext i
  dsimp [concreteInvNTT, concreteNTT]
  have h_expand :
      (∑ m : Fin N,
        (∑ j : Fin N, p.coeffs j * (oddRoot ψ m) ^ (j : ℕ)) *
          ψ_inv ^ ((2 * (m : ℕ) + 1) * (i : ℕ))) =
      ∑ j : Fin N, p.coeffs j *
        (∑ m : Fin N, (oddRoot ψ m) ^ (j : ℕ) * ψ_inv ^ ((2 * (m : ℕ) + 1) * (i : ℕ))) := by
    have h1 :
        (∑ m : Fin N,
          (∑ j : Fin N, p.coeffs j * (oddRoot ψ m) ^ (j : ℕ)) *
            ψ_inv ^ ((2 * (m : ℕ) + 1) * (i : ℕ))) =
        ∑ m : Fin N, ∑ j : Fin N,
          p.coeffs j * ((oddRoot ψ m) ^ (j : ℕ) * ψ_inv ^ ((2 * (m : ℕ) + 1) * (i : ℕ))) := by
      apply Finset.sum_congr rfl
      intro m _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [h1, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.mul_sum]
  rw [h_expand, Finset.mul_sum]
  have h_orth_apply :
      (∑ j : Fin N,
        n_inv * (p.coeffs j *
          (∑ m : Fin N, (oddRoot ψ m) ^ (j : ℕ) * ψ_inv ^ ((2 * (m : ℕ) + 1) * (i : ℕ))))) =
      ∑ j : Fin N, if j = i then p.coeffs j else 0 := by
    apply Finset.sum_congr rfl
    intro j _
    have h_j :
        n_inv * (p.coeffs j *
          (∑ m : Fin N, (oddRoot ψ m) ^ (j : ℕ) * ψ_inv ^ ((2 * (m : ℕ) + 1) * (i : ℕ)))) =
        p.coeffs j *
          (n_inv * (∑ m : Fin N,
            (oddRoot ψ m) ^ (j : ℕ) * ψ_inv ^ ((2 * (m : ℕ) + 1) * (i : ℕ)))) := by
      ring
    rw [h_j, h_orth j i]
    split_ifs <;> ring
  rw [h_orth_apply]
  simp

theorem concrete_ntt_mul_eq_mulSchoolbook [Fact (0 < N)] (ψ ψ_inv n_inv : R)
    (hpsi : ψ ^ N = -1) (h_orth : IsValidNTTInverse N ψ ψ_inv n_inv)
    (p q : NegacyclicPoly R N) :
    concreteInvNTT ψ_inv n_inv (concreteNTT ψ p * concreteNTT ψ q) = p * q := by
  rw [← concreteNTT_map_mul ψ hpsi p q]
  exact concreteInvNTT_concreteNTT ψ ψ_inv n_inv h_orth (p * q)

theorem concrete_ntt_mul_eq_mulSchoolbook_of_primitive [Fact (0 < N)] [NoZeroDivisors R]
    (ψ ψ_inv n_inv : R) (hpsi : ψ ^ N = -1) (h_inv : ψ * ψ_inv = 1) (hn : n_inv * (N : R) = 1)
    (h_prim : ∀ j i : Fin N, j ≠ i → ψ ^ (2 * (j : ℕ)) * ψ_inv ^ (2 * (i : ℕ)) ≠ 1)
    (p q : NegacyclicPoly R N) :
    concreteInvNTT ψ_inv n_inv (concreteNTT ψ p * concreteNTT ψ q) = p * q :=
  concrete_ntt_mul_eq_mulSchoolbook ψ ψ_inv n_inv hpsi
    (isValidNTTInverse_of_primitive ψ ψ_inv n_inv hpsi h_inv hn h_prim) p q

end ConcreteNTT

section ZKP

variable (R : Type*) [CommRing R]

structure ZKPPublicInfo where
  a : R
  t : R

structure ZKPSecretWitness where
  s : R
  e : R

def mkZKPPublicInfo (a : R) (wit : ZKPSecretWitness R) : ZKPPublicInfo R :=
  { a := a, t := a * wit.s + wit.e }

def zkpCommit (a y_s y_e : R) : R :=
  a * y_s + y_e

structure ZKPResponse where
  z_s : R
  z_e : R

def zkpRespond (y_s y_e c : R) (wit : ZKPSecretWitness R) : ZKPResponse R :=
  { z_s := y_s + c * wit.s,
    z_e := y_e + c * wit.e }

def zkpVerifyAlgebraic (pub : ZKPPublicInfo R) (c w : R) (resp : ZKPResponse R) : Prop :=
  pub.a * resp.z_s + resp.z_e - c * pub.t = w

theorem zkp_completeness (a y_s y_e c : R) (wit : ZKPSecretWitness R) :
    let pub := mkZKPPublicInfo R a wit
    let w := zkpCommit R a y_s y_e
    let resp := zkpRespond R y_s y_e c wit
    zkpVerifyAlgebraic R pub c w resp := by
  dsimp [mkZKPPublicInfo, zkpCommit, zkpRespond, zkpVerifyAlgebraic]
  ring

theorem zkp_special_soundness (pub : ZKPPublicInfo R) (c1 c2 w : R)
    (resp1 resp2 : ZKPResponse R)
    (h1 : zkpVerifyAlgebraic R pub c1 w resp1)
    (h2 : zkpVerifyAlgebraic R pub c2 w resp2) :
    pub.a * (resp1.z_s - resp2.z_s) + (resp1.z_e - resp2.z_e) = (c1 - c2) * pub.t := by
  dsimp [zkpVerifyAlgebraic] at h1 h2
  calc
    pub.a * (resp1.z_s - resp2.z_s) + (resp1.z_e - resp2.z_e)
      = (pub.a * resp1.z_s + resp1.z_e - c1 * pub.t) -
        (pub.a * resp2.z_s + resp2.z_e - c2 * pub.t) + (c1 - c2) * pub.t := by ring
    _ = w - w + (c1 - c2) * pub.t := by rw [h1, h2]
    _ = (c1 - c2) * pub.t := by ring

class HasInfinityNorm (R : Type*) [AddGroup R] where
  normInf : R → ℕ
  normInf_add_le : ∀ x y : R, normInf (x + y) ≤ normInf x + normInf y
  normInf_neg : ∀ x : R, normInf (-x) = normInf x

instance instHasInfinityNormZq (params : LWEParams) : HasInfinityNorm (Zq params) where
  normInf := norm params
  normInf_add_le := norm_add_le_elem params
  normInf_neg := norm_neg_elem params

instance instHasInfinityNormVectorZq (params : LWEParams) (len : ℕ) :
    HasInfinityNorm (VectorR (Zq params) len) where
  normInf := normInf params
  normInf_add_le := norm_add_le params
  normInf_neg := norm_neg params

instance instHasInfinityNormNegacyclicPolyZq (params : LWEParams) (N : ℕ) :
    HasInfinityNorm (NegacyclicPoly (Zq params) N) where
  normInf p := normInf params p.coeffs
  normInf_add_le p q := norm_add_le params p.coeffs q.coeffs
  normInf_neg p := norm_neg params p.coeffs

variable [HasInfinityNorm R]

lemma normInf_sub_le (x y : R) :
    HasInfinityNorm.normInf (x - y) ≤ HasInfinityNorm.normInf x + HasInfinityNorm.normInf y := by
  rw [sub_eq_add_neg, ← HasInfinityNorm.normInf_neg y]
  exact HasInfinityNorm.normInf_add_le x (-y)

def isSafeResponse (resp : ZKPResponse R) (bound : ℕ) : Bool :=
  HasInfinityNorm.normInf resp.z_s ≤ bound ∧ HasInfinityNorm.normInf resp.z_e ≤ bound

def zkpVerifyBound (resp : ZKPResponse R) (bound : ℕ) : Bool :=
  HasInfinityNorm.normInf resp.z_s ≤ bound ∧ HasInfinityNorm.normInf resp.z_e ≤ bound

theorem safe_response_passes_verify (resp : ZKPResponse R) (bound : ℕ) :
    isSafeResponse R resp bound = true → zkpVerifyBound R resp bound = true := by
  intro h
  exact h

theorem zkp_respond_passes_verify_of_mask_bound
    (y_s y_e c : R) (wit : ZKPSecretWitness R) (safe_bound beta : ℕ)
    (hys : HasInfinityNorm.normInf y_s + beta ≤ safe_bound)
    (hye : HasInfinityNorm.normInf y_e + beta ≤ safe_bound)
    (hcs : HasInfinityNorm.normInf (c * wit.s) ≤ beta)
    (hce : HasInfinityNorm.normInf (c * wit.e) ≤ beta) :
    zkpVerifyBound R (zkpRespond R y_s y_e c wit) safe_bound = true := by
  dsimp [zkpVerifyBound, zkpRespond]
  rw [decide_eq_true_iff]
  have hzs := HasInfinityNorm.normInf_add_le y_s (c * wit.s)
  have hze := HasInfinityNorm.normInf_add_le y_e (c * wit.e)
  constructor <;> omega

theorem zkp_extracted_norm_bound
    (resp1 resp2 : ZKPResponse R) (safe_bound : ℕ)
    (hb1 : zkpVerifyBound R resp1 safe_bound = true)
    (hb2 : zkpVerifyBound R resp2 safe_bound = true) :
    HasInfinityNorm.normInf (resp1.z_s - resp2.z_s) ≤ 2 * safe_bound ∧
    HasInfinityNorm.normInf (resp1.z_e - resp2.z_e) ≤ 2 * safe_bound := by
  dsimp [zkpVerifyBound] at hb1 hb2
  rw [decide_eq_true_iff] at hb1 hb2
  have h_sub_s := normInf_sub_le R resp1.z_s resp2.z_s
  have h_sub_e := normInf_sub_le R resp1.z_e resp2.z_e
  constructor <;> omega

theorem concrete_zkp_respond_passes_verify
    (params : LWEParams) (N safe_bound beta B_w : ℕ) [Fact (0 < N)]
    (y_s y_e c : NegacyclicPoly (Zq params) N)
    (wit : ZKPSecretWitness (NegacyclicPoly (Zq params) N))
    (hc : NegacyclicPoly.IsTernaryPoly c)
    (hs : normInf params wit.s.coeffs ≤ B_w)
    (he : normInf params wit.e.coeffs ≤ B_w)
    (hbeta : N * B_w ≤ beta)
    (hys : normInf params y_s.coeffs + beta ≤ safe_bound)
    (hye : normInf params y_e.coeffs + beta ≤ safe_bound) :
    zkpVerifyBound (NegacyclicPoly (Zq params) N)
      (zkpRespond (NegacyclicPoly (Zq params) N) y_s y_e c wit) safe_bound = true := by
  apply zkp_respond_passes_verify_of_mask_bound (NegacyclicPoly (Zq params) N)
    y_s y_e c wit safe_bound beta hys hye
  · have h_mul := NegacyclicPoly.normInf_ternary_mul_le params N c wit.s hc
    have h_le : N * normInf params wit.s.coeffs ≤ N * B_w := Nat.mul_le_mul_left N hs
    change normInf params (c * wit.s).coeffs ≤ beta
    omega
  · have h_mul := NegacyclicPoly.normInf_ternary_mul_le params N c wit.e hc
    have h_le : N * normInf params wit.e.coeffs ≤ N * B_w := Nat.mul_le_mul_left N he
    change normInf params (c * wit.e).coeffs ≤ beta
    omega

end ZKP

section ModuleZKP

variable (R : Type*) [CommRing R]
variable (n m : ℕ)

open scoped BigOperators

structure ModZKPPublicInfo where
  A : MatrixR R n m
  t : VectorR R m

structure ModZKPSecretWitness where
  s : VectorR R n
  e : VectorR R m

def mkModZKPPublicInfo (A : MatrixR R n m) (wit : ModZKPSecretWitness R n m) :
    ModZKPPublicInfo R n m :=
  { A := A, t := evaluate R n m A wit.s wit.e }

def modZkpCommit (A : MatrixR R n m) (y_s : VectorR R n) (y_e : VectorR R m) : VectorR R m :=
  evaluate R n m A y_s y_e

structure ModZKPResponse where
  z_s : VectorR R n
  z_e : VectorR R m

def modZkpRespond (y_s : VectorR R n) (y_e : VectorR R m) (c : R)
    (wit : ModZKPSecretWitness R n m) : ModZKPResponse R n m :=
  { z_s := fun i => y_s i + c * wit.s i,
    z_e := fun i => y_e i + c * wit.e i }

def modZkpVerifyAlgebraic (pub : ModZKPPublicInfo R n m) (c : R) (w : VectorR R m)
    (resp : ModZKPResponse R n m) : Prop :=
  (fun i => (∑ j, pub.A i j * resp.z_s j) + resp.z_e i - c * pub.t i) = w

theorem mod_zkp_completeness (A : MatrixR R n m) (y_s : VectorR R n) (y_e : VectorR R m) (c : R)
    (wit : ModZKPSecretWitness R n m) :
    let pub := mkModZKPPublicInfo R n m A wit
    let w := modZkpCommit R n m A y_s y_e
    let resp := modZkpRespond R n m y_s y_e c wit
    modZkpVerifyAlgebraic R n m pub c w resp := by
  dsimp [mkModZKPPublicInfo, modZkpCommit, modZkpRespond, modZkpVerifyAlgebraic]
  ext i
  simp only [evaluate, mul_add, Finset.sum_add_distrib, sub_eq_add_neg]
  have h_inner : ∀ x, A i x * (c * wit.s x) = c * (A i x * wit.s x) := by intro x; ring
  simp_rw [h_inner, ← Finset.mul_sum]
  ring

theorem mod_zkp_special_soundness (pub : ModZKPPublicInfo R n m) (c1 c2 : R) (w : VectorR R m)
    (resp1 resp2 : ModZKPResponse R n m)
    (h1 : modZkpVerifyAlgebraic R n m pub c1 w resp1)
    (h2 : modZkpVerifyAlgebraic R n m pub c2 w resp2) :
    evaluate R n m pub.A (resp1.z_s - resp2.z_s) (resp1.z_e - resp2.z_e) =
      fun i => (c1 - c2) * pub.t i := by
  ext i
  have h1_i := congrFun h1 i
  have h2_i := congrFun h2 i
  dsimp [evaluate]
  simp only [mul_sub, Finset.sum_sub_distrib]
  calc
    (∑ x, pub.A i x * resp1.z_s x - ∑ x, pub.A i x * resp2.z_s x) + (resp1.z_e i - resp2.z_e i)
      = ((∑ x, pub.A i x * resp1.z_s x) + resp1.z_e i - c1 * pub.t i) -
        ((∑ x, pub.A i x * resp2.z_s x) + resp2.z_e i - c2 * pub.t i) +
        (c1 - c2) * pub.t i := by ring
    _ = w i - w i + (c1 - c2) * pub.t i := by rw [h1_i, h2_i]
    _ = (c1 - c2) * pub.t i := by ring

variable [HasInfinityNorm R]

def modZkpVerifyBound (resp : ModZKPResponse R n m) (bound : ℕ) : Prop :=
  (∀ j : Fin n, HasInfinityNorm.normInf (resp.z_s j) ≤ bound) ∧
  (∀ i : Fin m, HasInfinityNorm.normInf (resp.z_e i) ≤ bound)

theorem mod_zkp_respond_passes_verify_of_mask_bound
    (y_s : VectorR R n) (y_e : VectorR R m) (c : R)
    (wit : ModZKPSecretWitness R n m) (safe_bound beta : ℕ)
    (hys : ∀ j : Fin n, HasInfinityNorm.normInf (y_s j) + beta ≤ safe_bound)
    (hye : ∀ i : Fin m, HasInfinityNorm.normInf (y_e i) + beta ≤ safe_bound)
    (hcs : ∀ j : Fin n, HasInfinityNorm.normInf (c * wit.s j) ≤ beta)
    (hce : ∀ i : Fin m, HasInfinityNorm.normInf (c * wit.e i) ≤ beta) :
    modZkpVerifyBound R n m (modZkpRespond R n m y_s y_e c wit) safe_bound := by
  constructor
  · intro j
    change HasInfinityNorm.normInf (y_s j + c * wit.s j) ≤ safe_bound
    have h_tri := HasInfinityNorm.normInf_add_le (y_s j) (c * wit.s j)
    have h1 := hys j
    have h2 := hcs j
    omega
  · intro i
    change HasInfinityNorm.normInf (y_e i + c * wit.e i) ≤ safe_bound
    have h_tri := HasInfinityNorm.normInf_add_le (y_e i) (c * wit.e i)
    have h1 := hye i
    have h2 := hce i
    omega

theorem mod_zkp_extracted_norm_bound
    (resp1 resp2 : ModZKPResponse R n m) (safe_bound : ℕ)
    (hb1 : modZkpVerifyBound R n m resp1 safe_bound)
    (hb2 : modZkpVerifyBound R n m resp2 safe_bound) :
    (∀ j : Fin n, HasInfinityNorm.normInf ((resp1.z_s - resp2.z_s) j) ≤ 2 * safe_bound) ∧
    (∀ i : Fin m, HasInfinityNorm.normInf ((resp1.z_e - resp2.z_e) i) ≤ 2 * safe_bound) := by
  rcases hb1 with ⟨hs1, he1⟩
  rcases hb2 with ⟨hs2, he2⟩
  constructor
  · intro j
    simp only [Pi.sub_apply]
    have h_sub := normInf_sub_le R (resp1.z_s j) (resp2.z_s j)
    have h1 := hs1 j
    have h2 := hs2 j
    omega
  · intro i
    simp only [Pi.sub_apply]
    have h_sub := normInf_sub_le R (resp1.z_e i) (resp2.z_e i)
    have h1 := he1 i
    have h2 := he2 i
    omega

theorem concrete_mod_zkp_respond_passes_verify
    (params : LWEParams) (N safe_bound beta B_w : ℕ) [Fact (0 < N)]
    (y_s : VectorR (NegacyclicPoly (Zq params) N) n)
    (y_e : VectorR (NegacyclicPoly (Zq params) N) m)
    (c : NegacyclicPoly (Zq params) N)
    (wit : ModZKPSecretWitness (NegacyclicPoly (Zq params) N) n m)
    (hc : NegacyclicPoly.IsTernaryPoly c)
    (hs : ∀ j : Fin n, normInf params (wit.s j).coeffs ≤ B_w)
    (he : ∀ i : Fin m, normInf params (wit.e i).coeffs ≤ B_w)
    (hbeta : N * B_w ≤ beta)
    (hys : ∀ j : Fin n, normInf params (y_s j).coeffs + beta ≤ safe_bound)
    (hye : ∀ i : Fin m, normInf params (y_e i).coeffs + beta ≤ safe_bound) :
    modZkpVerifyBound (NegacyclicPoly (Zq params) N) n m
      (modZkpRespond (NegacyclicPoly (Zq params) N) n m y_s y_e c wit) safe_bound := by
  apply mod_zkp_respond_passes_verify_of_mask_bound (NegacyclicPoly (Zq params) N) n m
    y_s y_e c wit safe_bound beta hys hye
  · intro j
    have h_mul := NegacyclicPoly.normInf_ternary_mul_le params N c (wit.s j) hc
    have h_le : N * normInf params (wit.s j).coeffs ≤ N * B_w := Nat.mul_le_mul_left N (hs j)
    change normInf params (c * wit.s j).coeffs ≤ beta
    omega
  · intro i
    have h_mul := NegacyclicPoly.normInf_ternary_mul_le params N c (wit.e i) hc
    have h_le : N * normInf params (wit.e i).coeffs ≤ N * B_w := Nat.mul_le_mul_left N (he i)
    change normInf params (c * wit.e i).coeffs ≤ beta
    omega

end ModuleZKP

section ModuleNTT

variable (PolyR : Type*) [CommRing PolyR]
variable (ScalarR : Type*) [CommRing ScalarR]
variable (N : ℕ)
variable (ntt : NTTHom PolyR N ScalarR)
variable {n m : ℕ}

def vectorNTT (v : VectorR PolyR n) : VectorR (Fin N → ScalarR) n :=
  fun i => ntt.toFun (v i)

def matrixNTT (A : MatrixR PolyR n m) : MatrixR (Fin N → ScalarR) n m :=
  fun i j => ntt.toFun (A i j)

theorem module_ntt_correct (A : MatrixR PolyR n m) (s : VectorR PolyR n) (e : VectorR PolyR m) :
    vectorNTT PolyR ScalarR N ntt (evaluate PolyR n m A s e) =
    evaluate (Fin N → ScalarR) n m (matrixNTT PolyR ScalarR N ntt A)
                                   (vectorNTT PolyR ScalarR N ntt s)
                                   (vectorNTT PolyR ScalarR N ntt e) := by
  ext i k
  dsimp [vectorNTT, matrixNTT, evaluate]
  have h_add := congrFun (ntt.map_add (∑ j, A i j * s j) (e i)) k
  have h_sum := congrFun (ntt.map_sum Finset.univ (fun j => A i j * s j)) k
  rw [h_add, Pi.add_apply, h_sum, Finset.sum_apply, Finset.sum_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [Pi.mul_apply]
  exact congrFun (ntt.map_mul (A i j) (s j)) k

def vectorInvNTT {R : Type*} [CommRing R] {N m : ℕ}
    (ψ_inv n_inv : R) (v : VectorR (Fin N → R) m) : VectorR (NegacyclicPoly R N) m :=
  fun i => concreteInvNTT ψ_inv n_inv (v i)

theorem concrete_module_ntt_eval_eq {R : Type*} [CommRing R] {N n m : ℕ} [Fact (0 < N)]
    (ψ ψ_inv n_inv : R) (hpsi : ψ ^ N = -1) (h_orth : IsValidNTTInverse N ψ ψ_inv n_inv)
    (A : MatrixR (NegacyclicPoly R N) n m)
    (s : VectorR (NegacyclicPoly R N) n)
    (e : VectorR (NegacyclicPoly R N) m) :
    let ntt := concreteNTTHom ψ hpsi
    vectorInvNTT ψ_inv n_inv
      (evaluate (Fin N → R) n m
        (matrixNTT (NegacyclicPoly R N) R N ntt A)
        (vectorNTT (NegacyclicPoly R N) R N ntt s)
        (vectorNTT (NegacyclicPoly R N) R N ntt e)) =
    evaluate (NegacyclicPoly R N) n m A s e := by
  intro ntt
  rw [← module_ntt_correct (NegacyclicPoly R N) R N ntt A s e]
  ext i k
  dsimp [vectorInvNTT, vectorNTT, concreteNTTHom]
  exact congrFun (congrArg NegacyclicPoly.coeffs
    (concreteInvNTT_concreteNTT ψ ψ_inv n_inv h_orth (evaluate (NegacyclicPoly R N) n m A s e i))) k

end ModuleNTT

section BFVFHE

open scoped BigOperators

section AlgebraicBFV

variable (R : Type*) [CommRing R]

structure BFVPublicKey where
  a : R
  b : R

structure BFVCiphertext where
  c0 : R
  c1 : R

def bfvKeygen (a s e : R) : BFVPublicKey R :=
  { a := a, b := -(a * s + e) }

def bfvEncrypt (pk : BFVPublicKey R) (u e0 e1 delta_m : R) : BFVCiphertext R :=
  { c0 := pk.b * u + e0 + delta_m,
    c1 := pk.a * u + e1 }

def bfvPhase (ct : BFVCiphertext R) (s : R) : R :=
  ct.c0 + ct.c1 * s

theorem bfvEncrypt_phase (a s e u e0 e1 delta_m : R) :
    bfvPhase R (bfvEncrypt R (bfvKeygen R a s e) u e0 e1 delta_m) s =
      delta_m + (e0 + e1 * s - e * u) := by
  dsimp [bfvPhase, bfvEncrypt, bfvKeygen]
  ring

def bfvAdd (ct1 ct2 : BFVCiphertext R) : BFVCiphertext R :=
  { c0 := ct1.c0 + ct2.c0,
    c1 := ct1.c1 + ct2.c1 }

theorem bfvAdd_phase (ct1 ct2 : BFVCiphertext R) (s : R) :
    bfvPhase R (bfvAdd R ct1 ct2) s = bfvPhase R ct1 s + bfvPhase R ct2 s := by
  dsimp [bfvPhase, bfvAdd]
  ring

def bfvSub (ct1 ct2 : BFVCiphertext R) : BFVCiphertext R :=
  { c0 := ct1.c0 - ct2.c0,
    c1 := ct1.c1 - ct2.c1 }

theorem bfvSub_phase (ct1 ct2 : BFVCiphertext R) (s : R) :
    bfvPhase R (bfvSub R ct1 ct2) s = bfvPhase R ct1 s - bfvPhase R ct2 s := by
  dsimp [bfvPhase, bfvSub]
  ring

def bfvAddPlain (ct : BFVCiphertext R) (delta_m : R) : BFVCiphertext R :=
  { c0 := ct.c0 + delta_m,
    c1 := ct.c1 }

theorem bfvAddPlain_phase (ct : BFVCiphertext R) (delta_m s : R) :
    bfvPhase R (bfvAddPlain R ct delta_m) s = bfvPhase R ct s + delta_m := by
  dsimp [bfvPhase, bfvAddPlain]
  ring

def bfvSubPlain (ct : BFVCiphertext R) (delta_m : R) : BFVCiphertext R :=
  { c0 := ct.c0 - delta_m,
    c1 := ct.c1 }

theorem bfvSubPlain_phase (ct : BFVCiphertext R) (delta_m s : R) :
    bfvPhase R (bfvSubPlain R ct delta_m) s = bfvPhase R ct s - delta_m := by
  dsimp [bfvPhase, bfvSubPlain]
  ring

def bfvMulPlain (ct : BFVCiphertext R) (pt : R) : BFVCiphertext R :=
  { c0 := ct.c0 * pt,
    c1 := ct.c1 * pt }

theorem bfvMulPlain_phase (ct : BFVCiphertext R) (pt s : R) :
    bfvPhase R (bfvMulPlain R ct pt) s = bfvPhase R ct s * pt := by
  dsimp [bfvPhase, bfvMulPlain]
  ring

def mkBFVGadgetRelinKey {l : ℕ} (a_rk e_rk : VectorR R l) (s : R) (G : VectorR R l) :
    GadgetRelinKey R l :=
  { a_rk := a_rk,
    b_rk := fun i => -(a_rk i * s + e_rk i) + G i * (s * s) }

def bfvGadgetRelinearize {l : ℕ} (d0 d1 d2 : R) (decomp : R → VectorR R l)
    (rk : GadgetRelinKey R l) : BFVCiphertext R :=
  let d2_dec := decomp d2
  { c0 := d0 + (∑ i, d2_dec i * rk.b_rk i),
    c1 := d1 + (∑ i, d2_dec i * rk.a_rk i) }

theorem bfvGadgetRelinearize_phase {l : ℕ} (s d0 d1 d2 : R)
    (a_rk e_rk G : VectorR R l) (decomp : R → VectorR R l)
    (h_dec : IsValidDecomposition G decomp) :
    let rk := mkBFVGadgetRelinKey R a_rk e_rk s G
    let ct_relin := bfvGadgetRelinearize R d0 d1 d2 decomp rk
    bfvPhase R ct_relin s =
      (d0 + d1 * s + d2 * (s * s)) - (∑ i, decomp d2 i * e_rk i) := by
  dsimp [mkBFVGadgetRelinKey, bfvGadgetRelinearize, bfvPhase]
  simp only [sub_eq_add_neg, neg_add, mul_add, add_mul, mul_neg, Finset.sum_add_distrib,
    Finset.sum_neg_distrib]
  have h1 : (∑ i : Fin l, decomp d2 i * (a_rk i * s)) =
      (∑ i : Fin l, decomp d2 i * a_rk i) * s := by
    simp_rw [← mul_assoc, Finset.sum_mul]
  have h2 : (∑ i : Fin l, decomp d2 i * (G i * (s * s))) =
      (∑ i : Fin l, decomp d2 i * G i) * (s * s) := by
    simp_rw [← mul_assoc, Finset.sum_mul]
  rw [h1, h2, h_dec d2]
  ring

end AlgebraicBFV

section ConcreteBFVDecryption

variable (params : LWEParams)

def bfvEncodeElem (Δ m : ℕ) : Zq params :=
  ((Δ * m : ℕ) : Zq params)

def bfvDecodeElem (Δ : ℕ) (y : Zq params) : ℕ :=
  ZMod.val (y + ((Δ / 2 : ℕ) : Zq params)) / Δ

lemma decode_of_natCast_eq (Δ t m r : ℕ) (y : Zq params)
    (ht_le : Δ * t ≤ params.q) (hm : m < t) (hr : r < Δ)
    (hy : y + ((Δ / 2 : ℕ) : Zq params) = ((Δ * m + r : ℕ) : Zq params)) :
    bfvDecodeElem params Δ y = m := by
  haveI : NeZero params.q := ⟨ne_of_gt params.q_pos.out⟩
  have hΔ_pos : 0 < Δ := by omega
  have h_mul_le : Δ * (m + 1) ≤ Δ * t := Nat.mul_le_mul_left Δ hm
  have h_mul_succ : Δ * (m + 1) = Δ * m + Δ := Nat.mul_succ Δ m
  have h_lt_q : Δ * m + r < params.q := by omega
  unfold bfvDecodeElem
  rw [hy, ZMod.val_natCast_of_lt h_lt_q]
  have h_comm : Δ * m + r = r + Δ * m := Nat.add_comm _ _
  rw [h_comm, Nat.add_mul_div_left r m hΔ_pos, Nat.div_eq_of_lt hr, Nat.zero_add]

theorem bfvDecodeElem_correct (Δ t m : ℕ) (e : Zq params)
    (ht_le : Δ * t ≤ params.q) (hm : m < t) (he : 2 * norm params e < Δ) :
    bfvDecodeElem params Δ (bfvEncodeElem params Δ m + e) = m := by
  haveI : NeZero params.q := ⟨ne_of_gt params.q_pos.out⟩
  have he_lt_q : ZMod.val e < params.q := ZMod.val_lt e
  have h_norm : norm params e =
      if (ZMod.val e : ℤ) ≤ (params.q : ℤ) / 2 then ZMod.val e else params.q - ZMod.val e := by
    unfold norm centeredLift
    dsimp
    split_ifs <;> omega
  by_cases h_half : (ZMod.val e : ℤ) ≤ (params.q : ℤ) / 2
  · rw [if_pos h_half] at h_norm
    let r : ℕ := ZMod.val e + Δ / 2
    have hr : r < Δ := by omega
    apply decode_of_natCast_eq params Δ t m r (bfvEncodeElem params Δ m + e) ht_le hm hr
    dsimp [bfvEncodeElem, r]
    push_cast
    rw [ZMod.natCast_zmod_val e]
    ring
  · rw [if_neg h_half] at h_norm
    let r : ℕ := Δ / 2 - (params.q - ZMod.val e)
    have hr : r < Δ := by omega
    have hr_add_q : r + params.q = ZMod.val e + Δ / 2 := by omega
    apply decode_of_natCast_eq params Δ t m r (bfvEncodeElem params Δ m + e) ht_le hm hr
    dsimp [bfvEncodeElem]
    have h_mod_q : ((Δ * m + r : ℕ) : Zq params) =
        (((Δ * m + (r + params.q) : ℕ) : Zq params)) := by
      push_cast
      rw [ZMod.natCast_self, add_zero]
    rw [h_mod_q, hr_add_q]
    push_cast
    rw [ZMod.natCast_zmod_val e]
    ring

def bfvEncodePoly (N Δ : ℕ) (m : Fin N → ℕ) : NegacyclicPoly (Zq params) N :=
  ⟨fun k => bfvEncodeElem params Δ (m k)⟩

def bfvDecodePoly (N Δ : ℕ) (p : NegacyclicPoly (Zq params) N) : Fin N → ℕ :=
  fun k => bfvDecodeElem params Δ (p.coeffs k)

def bfvDecryptPoly (N Δ : ℕ) [Fact (0 < N)]
    (s : NegacyclicPoly (Zq params) N)
    (ct : BFVCiphertext (NegacyclicPoly (Zq params) N)) : Fin N → ℕ :=
  bfvDecodePoly params N Δ (bfvPhase (NegacyclicPoly (Zq params) N) ct s)

theorem bfvDecryptPoly_of_phase_eq (N Δ t : ℕ) [Fact (0 < N)]
    (s E : NegacyclicPoly (Zq params) N)
    (ct : BFVCiphertext (NegacyclicPoly (Zq params) N))
    (m : Fin N → ℕ)
    (ht_le : Δ * t ≤ params.q)
    (hm : ∀ k : Fin N, m k < t)
    (h_phase : bfvPhase (NegacyclicPoly (Zq params) N) ct s = bfvEncodePoly params N Δ m + E)
    (h_noise : 2 * normInf params E.coeffs < Δ) :
    bfvDecryptPoly params N Δ s ct = m := by
  ext k
  unfold bfvDecryptPoly bfvDecodePoly
  rw [h_phase, NegacyclicPoly.add_coeffs]
  dsimp [bfvEncodePoly]
  have hk_le : norm params (E.coeffs k) ≤ normInf params E.coeffs :=
    Finset.le_sup (f := fun j => norm params (E.coeffs j)) (Finset.mem_univ k)
  have hk_noise : 2 * norm params (E.coeffs k) < Δ := by omega
  exact bfvDecodeElem_correct params Δ t (m k) (E.coeffs k) ht_le (hm k) hk_noise

theorem bfvDecryptPoly_encrypt_correct (N Δ t : ℕ) [Fact (0 < N)]
    (a s e u e0 e1 : NegacyclicPoly (Zq params) N)
    (m : Fin N → ℕ)
    (ht_le : Δ * t ≤ params.q)
    (hm : ∀ k : Fin N, m k < t)
    (h_noise : 2 * normInf params (e0 + e1 * s - e * u).coeffs < Δ) :
    let pk := bfvKeygen (NegacyclicPoly (Zq params) N) a s e
    let ct := bfvEncrypt (NegacyclicPoly (Zq params) N) pk u e0 e1 (bfvEncodePoly params N Δ m)
    bfvDecryptPoly params N Δ s ct = m := by
  intro pk ct
  apply bfvDecryptPoly_of_phase_eq params N Δ t s (e0 + e1 * s - e * u) ct m ht_le hm
  · exact bfvEncrypt_phase (NegacyclicPoly (Zq params) N) a s e u e0 e1 (bfvEncodePoly params N Δ m)
  · exact h_noise

theorem bfvDecryptPoly_add_correct (N Δ t : ℕ) [Fact (0 < N)]
    (s E1 E2 : NegacyclicPoly (Zq params) N)
    (ct1 ct2 : BFVCiphertext (NegacyclicPoly (Zq params) N))
    (m1 m2 : Fin N → ℕ)
    (ht_le : Δ * t ≤ params.q)
    (hm : ∀ k : Fin N, m1 k + m2 k < t)
    (h_phase1 : bfvPhase (NegacyclicPoly (Zq params) N) ct1 s = bfvEncodePoly params N Δ m1 + E1)
    (h_phase2 : bfvPhase (NegacyclicPoly (Zq params) N) ct2 s = bfvEncodePoly params N Δ m2 + E2)
    (h_noise : 2 * (normInf params E1.coeffs + normInf params E2.coeffs) < Δ) :
    bfvDecryptPoly params N Δ s (bfvAdd (NegacyclicPoly (Zq params) N) ct1 ct2) =
      fun k => m1 k + m2 k := by
  have h_encode_add :
      bfvEncodePoly params N Δ m1 + bfvEncodePoly params N Δ m2 =
        bfvEncodePoly params N Δ (fun k => m1 k + m2 k) := by
    ext k
    simp only [NegacyclicPoly.add_coeffs, bfvEncodePoly, bfvEncodeElem, Nat.mul_add, Nat.cast_add]
  have h_phase_sum :
      bfvPhase (NegacyclicPoly (Zq params) N) (bfvAdd (NegacyclicPoly (Zq params) N) ct1 ct2) s =
        bfvEncodePoly params N Δ (fun k => m1 k + m2 k) + (E1 + E2) := by
    rw [bfvAdd_phase, h_phase1, h_phase2, ← h_encode_add]
    ring
  have h_tri := norm_add_le params E1.coeffs E2.coeffs
  have h_noise_sum : 2 * normInf params (E1 + E2).coeffs < Δ := by
    change 2 * normInf params (E1.coeffs + E2.coeffs) < Δ
    omega
  exact bfvDecryptPoly_of_phase_eq params N Δ t s (E1 + E2)
    (bfvAdd (NegacyclicPoly (Zq params) N) ct1 ct2) (fun k => m1 k + m2 k)
    ht_le hm h_phase_sum h_noise_sum

theorem concrete_bfvGadgetRelinearize_phase {N B l : ℕ} [Fact (0 < N)]
    (hq : params.q ≤ B ^ l)
    (s d0 d1 d2 : NegacyclicPoly (Zq params) N)
    (a_rk e_rk : VectorR (NegacyclicPoly (Zq params) N) l) :
    let rk := mkBFVGadgetRelinKey (NegacyclicPoly (Zq params) N) a_rk e_rk s
      (NegacyclicPoly.negacyclicGadget params N B l)
    let ct_relin := bfvGadgetRelinearize (NegacyclicPoly (Zq params) N) d0 d1 d2
      (NegacyclicPoly.negacyclicDecomp params N B l) rk
    bfvPhase (NegacyclicPoly (Zq params) N) ct_relin s =
      (d0 + d1 * s + d2 * (s * s)) -
        (∑ i, NegacyclicPoly.negacyclicDecomp params N B l d2 i * e_rk i) :=
  bfvGadgetRelinearize_phase (NegacyclicPoly (Zq params) N) s d0 d1 d2 a_rk e_rk
    (NegacyclicPoly.negacyclicGadget params N B l)
    (NegacyclicPoly.negacyclicDecomp params N B l)
    (NegacyclicPoly.negacyclicDecomp_isValid params N B l hq)

theorem bfvDecryptPoly_mul_correct (N Δ t B l : ℕ) [Fact (0 < N)]
    (hq : params.q ≤ B ^ l)
    (s d0 d1 d2 E_scale : NegacyclicPoly (Zq params) N)
    (a_rk e_rk : VectorR (NegacyclicPoly (Zq params) N) l)
    (m_prod : Fin N → ℕ)
    (ht_le : Δ * t ≤ params.q)
    (hm : ∀ k : Fin N, m_prod k < t)
    (h_scale_phase : d0 + d1 * s + d2 * (s * s) = bfvEncodePoly params N Δ m_prod + E_scale)
    (h_noise : 2 * normInf params
      (E_scale - ∑ i, NegacyclicPoly.negacyclicDecomp params N B l d2 i * e_rk i).coeffs < Δ) :
    let rk := mkBFVGadgetRelinKey (NegacyclicPoly (Zq params) N) a_rk e_rk s
      (NegacyclicPoly.negacyclicGadget params N B l)
    let ct_mul := bfvGadgetRelinearize (NegacyclicPoly (Zq params) N) d0 d1 d2
      (NegacyclicPoly.negacyclicDecomp params N B l) rk
    bfvDecryptPoly params N Δ s ct_mul = m_prod := by
  intro rk ct_mul
  have h_relin := concrete_bfvGadgetRelinearize_phase params hq s d0 d1 d2 a_rk e_rk
  dsimp only at h_relin
  have h_phase :
      bfvPhase (NegacyclicPoly (Zq params) N) ct_mul s =
        bfvEncodePoly params N Δ m_prod +
          (E_scale - ∑ i, NegacyclicPoly.negacyclicDecomp params N B l d2 i * e_rk i) := by
    change bfvPhase (NegacyclicPoly (Zq params) N)
      (bfvGadgetRelinearize (NegacyclicPoly (Zq params) N) d0 d1 d2
        (NegacyclicPoly.negacyclicDecomp params N B l) rk) s = _
    rw [h_relin, h_scale_phase]
    ring
  exact bfvDecryptPoly_of_phase_eq params N Δ t s
    (E_scale - ∑ i, NegacyclicPoly.negacyclicDecomp params N B l d2 i * e_rk i)
    ct_mul m_prod ht_le hm h_phase h_noise

theorem bfvDecryptPoly_addPlain_correct (N Δ t : ℕ) [Fact (0 < N)]
    (s E : NegacyclicPoly (Zq params) N)
    (ct : BFVCiphertext (NegacyclicPoly (Zq params) N))
    (m1 m2 : Fin N → ℕ)
    (ht_le : Δ * t ≤ params.q)
    (hm : ∀ k : Fin N, m1 k + m2 k < t)
    (h_phase : bfvPhase (NegacyclicPoly (Zq params) N) ct s = bfvEncodePoly params N Δ m1 + E)
    (h_noise : 2 * normInf params E.coeffs < Δ) :
    bfvDecryptPoly params N Δ s
      (bfvAddPlain (NegacyclicPoly (Zq params) N) ct (bfvEncodePoly params N Δ m2)) =
      fun k => m1 k + m2 k := by
  have h_encode_add :
      bfvEncodePoly params N Δ m1 + bfvEncodePoly params N Δ m2 =
        bfvEncodePoly params N Δ (fun k => m1 k + m2 k) := by
    ext k
    simp only [NegacyclicPoly.add_coeffs, bfvEncodePoly, bfvEncodeElem, Nat.mul_add, Nat.cast_add]
  have h_phase_add :
      bfvPhase (NegacyclicPoly (Zq params) N)
        (bfvAddPlain (NegacyclicPoly (Zq params) N) ct (bfvEncodePoly params N Δ m2)) s =
        bfvEncodePoly params N Δ (fun k => m1 k + m2 k) + E := by
    rw [bfvAddPlain_phase, h_phase, ← h_encode_add]
    ring
  exact bfvDecryptPoly_of_phase_eq params N Δ t s E
    (bfvAddPlain (NegacyclicPoly (Zq params) N) ct (bfvEncodePoly params N Δ m2))
    (fun k => m1 k + m2 k) ht_le hm h_phase_add h_noise

theorem bfvDecryptPoly_mulPlain_correct (N Δ t : ℕ) [Fact (0 < N)]
    (s E pt : NegacyclicPoly (Zq params) N)
    (ct : BFVCiphertext (NegacyclicPoly (Zq params) N))
    (m1 m_prod : Fin N → ℕ)
    (ht_le : Δ * t ≤ params.q)
    (hm : ∀ k : Fin N, m_prod k < t)
    (h_phase : bfvPhase (NegacyclicPoly (Zq params) N) ct s = bfvEncodePoly params N Δ m1 + E)
    (h_encode_mul : bfvEncodePoly params N Δ m1 * pt = bfvEncodePoly params N Δ m_prod)
    (h_noise : 2 * normInf params (E * pt).coeffs < Δ) :
    bfvDecryptPoly params N Δ s (bfvMulPlain (NegacyclicPoly (Zq params) N) ct pt) = m_prod := by
  have h_phase_mul :
      bfvPhase (NegacyclicPoly (Zq params) N)
        (bfvMulPlain (NegacyclicPoly (Zq params) N) ct pt) s =
        bfvEncodePoly params N Δ m_prod + E * pt := by
    rw [bfvMulPlain_phase, h_phase, add_mul, h_encode_mul]
  exact bfvDecryptPoly_of_phase_eq params N Δ t s (E * pt)
    (bfvMulPlain (NegacyclicPoly (Zq params) N) ct pt) m_prod ht_le hm h_phase_mul h_noise

def bfvPhaseNTT {R : Type*} [CommRing R] {N : ℕ}
    (ψ ψ_inv n_inv : R) (ct : BFVCiphertext (NegacyclicPoly R N)) (s : NegacyclicPoly R N) :
    NegacyclicPoly R N :=
  ct.c0 + concreteInvNTT ψ_inv n_inv (concreteNTT ψ ct.c1 * concreteNTT ψ s)

theorem bfvPhaseNTT_eq_bfvPhase {R : Type*} [CommRing R] [NoZeroDivisors R] {N : ℕ} [Fact (0 < N)]
    (ψ ψ_inv n_inv : R) (hpsi : ψ ^ N = -1) (h_inv : ψ * ψ_inv = 1) (hn : n_inv * (N : R) = 1)
    (h_prim : ∀ j i : Fin N, j ≠ i → ψ ^ (2 * (j : ℕ)) * ψ_inv ^ (2 * (i : ℕ)) ≠ 1)
    (ct : BFVCiphertext (NegacyclicPoly R N)) (s : NegacyclicPoly R N) :
    bfvPhaseNTT ψ ψ_inv n_inv ct s = bfvPhase (NegacyclicPoly R N) ct s := by
  unfold bfvPhaseNTT bfvPhase
  rw [concrete_ntt_mul_eq_mulSchoolbook_of_primitive ψ ψ_inv n_inv hpsi h_inv hn h_prim ct.c1 s]

end ConcreteBFVDecryption

end BFVFHE

section ModulePKE

open scoped BigOperators

variable (R : Type*) [CommRing R]
variable (k : ℕ)

def transposeMatrix {n m : ℕ} (A : MatrixR R n m) : MatrixR R m n :=
  fun i j => A j i

def dotProductR (u v : VectorR R k) : R :=
  ∑ i : Fin k, u i * v i

theorem dotProduct_mulVec_transpose (A : MatrixR R k k) (s r : VectorR R k) :
    dotProductR R k (fun i => ∑ j : Fin k, A i j * s j) r =
      dotProductR R k s (fun j => ∑ i : Fin k, transposeMatrix R A j i * r i) := by
  dsimp [dotProductR, transposeMatrix]
  have h_lhs :
      (∑ i : Fin k, (∑ j : Fin k, A i j * s j) * r i) =
        ∑ i : Fin k, ∑ j : Fin k, A i j * s j * r i := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_mul]
  have h_rhs :
      (∑ j : Fin k, s j * ∑ i : Fin k, A i j * r i) =
        ∑ j : Fin k, ∑ i : Fin k, s j * (A i j * r i) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
  rw [h_lhs, h_rhs, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

structure ModPKEPublicKey where
  A : MatrixR R k k
  t : VectorR R k

structure ModPKECiphertext where
  u : VectorR R k
  v : R

def modPKEKeygen (A : MatrixR R k k) (s e : VectorR R k) : ModPKEPublicKey R k :=
  { A := A, t := evaluate R k k A s e }

def modPKEEncrypt (pk : ModPKEPublicKey R k) (r e1 : VectorR R k) (e2 delta_m : R) :
    ModPKECiphertext R k :=
  { u := evaluate R k k (transposeMatrix R pk.A) r e1,
    v := dotProductR R k pk.t r + e2 + delta_m }

def modPKEPhase (ct : ModPKECiphertext R k) (s : VectorR R k) : R :=
  ct.v - dotProductR R k s ct.u

theorem modPKE_phase_eq (A : MatrixR R k k) (s e r e1 : VectorR R k) (e2 delta_m : R) :
    modPKEPhase R k (modPKEEncrypt R k (modPKEKeygen R k A s e) r e1 e2 delta_m) s =
      delta_m + (dotProductR R k e r + e2 - dotProductR R k s e1) := by
  dsimp [modPKEPhase, modPKEEncrypt, modPKEKeygen]
  have h_tr :
      dotProductR R k (evaluate R k k A s e) r =
        dotProductR R k (fun i => ∑ j : Fin k, A i j * s j) r + dotProductR R k e r := by
    dsimp [dotProductR, evaluate]
    simp only [add_mul, Finset.sum_add_distrib]
  have h_su :
      dotProductR R k s (evaluate R k k (transposeMatrix R A) r e1) =
        dotProductR R k s (fun i => ∑ j : Fin k, transposeMatrix R A i j * r j) +
          dotProductR R k s e1 := by
    dsimp [dotProductR, evaluate]
    simp only [mul_add, Finset.sum_add_distrib]
  rw [h_tr, h_su, dotProduct_mulVec_transpose R k A s r]
  ring

theorem modPKE_decrypt_correct (params : LWEParams) (k N Δ t : ℕ) [Fact (0 < N)]
    (A : MatrixR (NegacyclicPoly (Zq params) N) k k)
    (s e r e1 : VectorR (NegacyclicPoly (Zq params) N) k)
    (e2 : NegacyclicPoly (Zq params) N)
    (m : Fin N → ℕ)
    (ht_le : Δ * t ≤ params.q)
    (hm : ∀ idx : Fin N, m idx < t)
    (h_noise : 2 * normInf params
      (dotProductR (NegacyclicPoly (Zq params) N) k e r + e2 -
        dotProductR (NegacyclicPoly (Zq params) N) k s e1).coeffs < Δ) :
    let pk := modPKEKeygen (NegacyclicPoly (Zq params) N) k A s e
    let ct := modPKEEncrypt (NegacyclicPoly (Zq params) N) k pk r e1 e2 (bfvEncodePoly params N Δ m)
    bfvDecodePoly params N Δ (modPKEPhase (NegacyclicPoly (Zq params) N) k ct s) = m := by
  intro pk ct
  have h_phase := modPKE_phase_eq (NegacyclicPoly (Zq params) N) k A s e r e1 e2
    (bfvEncodePoly params N Δ m)
  change bfvDecodePoly params N Δ (modPKEPhase (NegacyclicPoly (Zq params) N) k ct s) = m
  rw [h_phase]
  ext idx
  unfold bfvDecodePoly
  rw [NegacyclicPoly.add_coeffs]
  dsimp [bfvEncodePoly]
  set E := dotProductR (NegacyclicPoly (Zq params) N) k e r + e2 -
    dotProductR (NegacyclicPoly (Zq params) N) k s e1
  have h_le : norm params (E.coeffs idx) ≤ normInf params E.coeffs :=
    Finset.le_sup (f := fun j => norm params (E.coeffs j)) (Finset.mem_univ idx)
  have h_idx_noise : 2 * norm params (E.coeffs idx) < Δ := by omega
  exact bfvDecodeElem_correct params Δ t (m idx) (E.coeffs idx) ht_le (hm idx) h_idx_noise

def bfvNoise (ct : BFVCiphertext R) (s delta_m : R) : R :=
  bfvPhase R ct s - delta_m

theorem bfvNoise_encrypt (a s e u e0 e1 delta_m : R) :
    bfvNoise R (bfvEncrypt R (bfvKeygen R a s e) u e0 e1 delta_m) s delta_m =
      e0 + e1 * s - e * u := by
  dsimp [bfvNoise]
  rw [bfvEncrypt_phase]
  ring

theorem bfvNoise_add (ct1 ct2 : BFVCiphertext R) (s dm1 dm2 : R) :
    bfvNoise R (bfvAdd R ct1 ct2) s (dm1 + dm2) =
      bfvNoise R ct1 s dm1 + bfvNoise R ct2 s dm2 := by
  dsimp [bfvNoise]
  rw [bfvAdd_phase]
  ring

theorem bfvNoise_sub (ct1 ct2 : BFVCiphertext R) (s dm1 dm2 : R) :
    bfvNoise R (bfvSub R ct1 ct2) s (dm1 - dm2) =
      bfvNoise R ct1 s dm1 - bfvNoise R ct2 s dm2 := by
  dsimp [bfvNoise]
  rw [bfvSub_phase]
  ring

theorem bfvNoise_addPlain (ct : BFVCiphertext R) (s dm1 dm2 : R) :
    bfvNoise R (bfvAddPlain R ct dm2) s (dm1 + dm2) =
      bfvNoise R ct s dm1 := by
  dsimp [bfvNoise]
  rw [bfvAddPlain_phase]
  ring

theorem bfvNoise_subPlain (ct : BFVCiphertext R) (s dm1 dm2 : R) :
    bfvNoise R (bfvSubPlain R ct dm2) s (dm1 - dm2) =
      bfvNoise R ct s dm1 := by
  dsimp [bfvNoise]
  rw [bfvSubPlain_phase]
  ring

theorem bfvNoise_mulPlain (ct : BFVCiphertext R) (s dm pt : R) :
    bfvNoise R (bfvMulPlain R ct pt) s (dm * pt) =
      bfvNoise R ct s dm * pt := by
  dsimp [bfvNoise]
  rw [bfvMulPlain_phase]
  ring

theorem bfvAdd_noise_bound (params : LWEParams) (N : ℕ) [Fact (0 < N)]
    (ct1 ct2 : BFVCiphertext (NegacyclicPoly (Zq params) N))
    (s dm1 dm2 : NegacyclicPoly (Zq params) N) (B1 B2 : ℕ)
    (h1 : normInf params (bfvNoise (NegacyclicPoly (Zq params) N) ct1 s dm1).coeffs ≤ B1)
    (h2 : normInf params (bfvNoise (NegacyclicPoly (Zq params) N) ct2 s dm2).coeffs ≤ B2) :
    normInf params
      (bfvNoise (NegacyclicPoly (Zq params) N)
        (bfvAdd (NegacyclicPoly (Zq params) N) ct1 ct2) s (dm1 + dm2)).coeffs ≤ B1 + B2 := by
  rw [bfvNoise_add]
  have h_tri := norm_add_le params
    (bfvNoise (NegacyclicPoly (Zq params) N) ct1 s dm1).coeffs
    (bfvNoise (NegacyclicPoly (Zq params) N) ct2 s dm2).coeffs
  change normInf params
    ((bfvNoise (NegacyclicPoly (Zq params) N) ct1 s dm1).coeffs +
      (bfvNoise (NegacyclicPoly (Zq params) N) ct2 s dm2).coeffs) ≤ B1 + B2
  omega

theorem bfvSub_noise_bound (params : LWEParams) (N : ℕ) [Fact (0 < N)]
    (ct1 ct2 : BFVCiphertext (NegacyclicPoly (Zq params) N))
    (s dm1 dm2 : NegacyclicPoly (Zq params) N) (B1 B2 : ℕ)
    (h1 : normInf params (bfvNoise (NegacyclicPoly (Zq params) N) ct1 s dm1).coeffs ≤ B1)
    (h2 : normInf params (bfvNoise (NegacyclicPoly (Zq params) N) ct2 s dm2).coeffs ≤ B2) :
    normInf params
      (bfvNoise (NegacyclicPoly (Zq params) N)
        (bfvSub (NegacyclicPoly (Zq params) N) ct1 ct2) s (dm1 - dm2)).coeffs ≤ B1 + B2 := by
  rw [bfvNoise_sub]
  have h_tri := norm_sub_le params
    (bfvNoise (NegacyclicPoly (Zq params) N) ct1 s dm1).coeffs
    (bfvNoise (NegacyclicPoly (Zq params) N) ct2 s dm2).coeffs
  change normInf params
    ((bfvNoise (NegacyclicPoly (Zq params) N) ct1 s dm1).coeffs -
      (bfvNoise (NegacyclicPoly (Zq params) N) ct2 s dm2).coeffs) ≤ B1 + B2
  omega

def modKEMEncaps {Key Coins : Type*} (params : LWEParams) (k N Δ : ℕ) [Fact (0 < N)]
    (G : ModPKEPublicKey (NegacyclicPoly (Zq params) N) k → (Fin N → ℕ) → Key × Coins)
    (expandR : Coins → VectorR (NegacyclicPoly (Zq params) N) k)
    (expandE1 : Coins → VectorR (NegacyclicPoly (Zq params) N) k)
    (expandE2 : Coins → NegacyclicPoly (Zq params) N)
    (pk : ModPKEPublicKey (NegacyclicPoly (Zq params) N) k)
    (m : Fin N → ℕ) : ModPKECiphertext (NegacyclicPoly (Zq params) N) k × Key :=
  let kc := G pk m
  let ct := modPKEEncrypt (NegacyclicPoly (Zq params) N) k pk
    (expandR kc.2) (expandE1 kc.2) (expandE2 kc.2) (bfvEncodePoly params N Δ m)
  (ct, kc.1)

def modKEMDecaps {Key Coins Seed : Type*} (params : LWEParams) (k N Δ : ℕ) [Fact (0 < N)]
    [DecidableEq (ModPKECiphertext (NegacyclicPoly (Zq params) N) k)]
    (G : ModPKEPublicKey (NegacyclicPoly (Zq params) N) k → (Fin N → ℕ) → Key × Coins)
    (expandR : Coins → VectorR (NegacyclicPoly (Zq params) N) k)
    (expandE1 : Coins → VectorR (NegacyclicPoly (Zq params) N) k)
    (expandE2 : Coins → NegacyclicPoly (Zq params) N)
    (J : Seed → ModPKECiphertext (NegacyclicPoly (Zq params) N) k → Key)
    (pk : ModPKEPublicKey (NegacyclicPoly (Zq params) N) k)
    (s : VectorR (NegacyclicPoly (Zq params) N) k)
    (z : Seed)
    (ct : ModPKECiphertext (NegacyclicPoly (Zq params) N) k) : Key :=
  let m' := bfvDecodePoly params N Δ (modPKEPhase (NegacyclicPoly (Zq params) N) k ct s)
  let kc' := G pk m'
  let ct' := modPKEEncrypt (NegacyclicPoly (Zq params) N) k pk
    (expandR kc'.2) (expandE1 kc'.2) (expandE2 kc'.2) (bfvEncodePoly params N Δ m')
  if ct = ct' then kc'.1 else J z ct

theorem modKEM_correctness {Key Coins Seed : Type*} (params : LWEParams) (k N Δ t : ℕ)
    [Fact (0 < N)]
    [DecidableEq (ModPKECiphertext (NegacyclicPoly (Zq params) N) k)]
    (G : ModPKEPublicKey (NegacyclicPoly (Zq params) N) k → (Fin N → ℕ) → Key × Coins)
    (expandR : Coins → VectorR (NegacyclicPoly (Zq params) N) k)
    (expandE1 : Coins → VectorR (NegacyclicPoly (Zq params) N) k)
    (expandE2 : Coins → NegacyclicPoly (Zq params) N)
    (J : Seed → ModPKECiphertext (NegacyclicPoly (Zq params) N) k → Key)
    (A : MatrixR (NegacyclicPoly (Zq params) N) k k)
    (s e : VectorR (NegacyclicPoly (Zq params) N) k)
    (z : Seed)
    (m : Fin N → ℕ)
    (ht_le : Δ * t ≤ params.q)
    (hm : ∀ idx : Fin N, m idx < t)
    (h_noise :
      let pk := modPKEKeygen (NegacyclicPoly (Zq params) N) k A s e
      let coins := (G pk m).2
      2 * normInf params
        (dotProductR (NegacyclicPoly (Zq params) N) k e (expandR coins) + expandE2 coins -
          dotProductR (NegacyclicPoly (Zq params) N) k s (expandE1 coins)).coeffs < Δ) :
    let pk := modPKEKeygen (NegacyclicPoly (Zq params) N) k A s e
    let enc := modKEMEncaps params k N Δ G expandR expandE1 expandE2 pk m
    modKEMDecaps params k N Δ G expandR expandE1 expandE2 J pk s z enc.1 = enc.2 := by
  intro pk enc
  have h_dec :
      bfvDecodePoly params N Δ
        (modPKEPhase (NegacyclicPoly (Zq params) N) k enc.1 s) = m :=
    modPKE_decrypt_correct params k N Δ t A s e
      (expandR (G pk m).2) (expandE1 (G pk m).2) (expandE2 (G pk m).2) m ht_le hm h_noise
  change (let m' := bfvDecodePoly params N Δ (modPKEPhase (NegacyclicPoly (Zq params) N) k enc.1 s)
    let kc' := G pk m'
    let ct' := modPKEEncrypt (NegacyclicPoly (Zq params) N) k pk
      (expandR kc'.2) (expandE1 kc'.2) (expandE2 kc'.2) (bfvEncodePoly params N Δ m')
    if enc.1 = ct' then kc'.1 else J z enc.1) = (G pk m).1
  rw [h_dec]
  exact if_pos rfl

theorem modKEM_implicit_rejection {Key Coins Seed : Type*} (params : LWEParams) (k N Δ : ℕ)
    [Fact (0 < N)]
    [DecidableEq (ModPKECiphertext (NegacyclicPoly (Zq params) N) k)]
    (G : ModPKEPublicKey (NegacyclicPoly (Zq params) N) k → (Fin N → ℕ) → Key × Coins)
    (expandR : Coins → VectorR (NegacyclicPoly (Zq params) N) k)
    (expandE1 : Coins → VectorR (NegacyclicPoly (Zq params) N) k)
    (expandE2 : Coins → NegacyclicPoly (Zq params) N)
    (J : Seed → ModPKECiphertext (NegacyclicPoly (Zq params) N) k → Key)
    (pk : ModPKEPublicKey (NegacyclicPoly (Zq params) N) k)
    (s : VectorR (NegacyclicPoly (Zq params) N) k)
    (z : Seed)
    (ct : ModPKECiphertext (NegacyclicPoly (Zq params) N) k)
    (h_invalid :
      let m' := bfvDecodePoly params N Δ (modPKEPhase (NegacyclicPoly (Zq params) N) k ct s)
      let kc' := G pk m'
      ct ≠ modPKEEncrypt (NegacyclicPoly (Zq params) N) k pk
        (expandR kc'.2) (expandE1 kc'.2) (expandE2 kc'.2) (bfvEncodePoly params N Δ m')) :
    modKEMDecaps params k N Δ G expandR expandE1 expandE2 J pk s z ct = J z ct := by
  dsimp [modKEMDecaps]
  exact if_neg h_invalid

def modPKEEncryptionMatrix (pk : ModPKEPublicKey R k) : MatrixR R k (k + 1) :=
  Fin.snoc (α := fun _ => VectorR R k) (transposeMatrix R pk.A) pk.t

def modPKEExtendError (e1 : VectorR R k) (e2 : R) : VectorR R (k + 1) :=
  Fin.snoc (α := fun _ => R) e1 e2

def modPKECiphertextTarget (ct : ModPKECiphertext R k) (delta_m : R) : VectorR R (k + 1) :=
  Fin.snoc (α := fun _ => R) ct.u (ct.v - delta_m)

theorem modPKE_ciphertext_relation_correct (pk : ModPKEPublicKey R k)
    (r e1 : VectorR R k) (e2 delta_m : R) :
    evaluate R k (k + 1) (modPKEEncryptionMatrix R k pk) r (modPKEExtendError R k e1 e2) =
      modPKECiphertextTarget R k (modPKEEncrypt R k pk r e1 e2 delta_m) delta_m := by
  ext i
  refine Fin.lastCases ?_ ?_ i
  · dsimp [evaluate, modPKEEncryptionMatrix, modPKEExtendError, modPKECiphertextTarget,
      modPKEEncrypt, dotProductR]
    simp only [Fin.snoc_last]
    ring
  · intro j
    dsimp [evaluate, modPKEEncryptionMatrix, modPKEExtendError, modPKECiphertextTarget,
      modPKEEncrypt]
    simp only [Fin.snoc_castSucc]
    rfl

theorem verifiable_encrypt_completeness (params : LWEParams) (k N safe_bound beta : ℕ)
    [Fact (0 < N)]
    (pk : ModPKEPublicKey (NegacyclicPoly (Zq params) N) k)
    (r e1 : VectorR (NegacyclicPoly (Zq params) N) k)
    (e2 delta_m : NegacyclicPoly (Zq params) N)
    (y_r : VectorR (NegacyclicPoly (Zq params) N) k)
    (y_e : VectorR (NegacyclicPoly (Zq params) N) (k + 1))
    (c : NegacyclicPoly (Zq params) N)
    (hc : NegacyclicPoly.IsTernaryPoly c)
    (hr : ∀ j : Fin k, normInf params (r j).coeffs ≤ 1)
    (he1 : ∀ i : Fin k, normInf params (e1 i).coeffs ≤ 1)
    (he2 : normInf params e2.coeffs ≤ 1)
    (hbeta : N * 1 ≤ beta)
    (h_yr : ∀ j : Fin k, normInf params (y_r j).coeffs + beta ≤ safe_bound)
    (h_ye : ∀ i : Fin (k + 1), normInf params (y_e i).coeffs + beta ≤ safe_bound) :
    let ct := modPKEEncrypt (NegacyclicPoly (Zq params) N) k pk r e1 e2 delta_m
    let M_enc := modPKEEncryptionMatrix (NegacyclicPoly (Zq params) N) k pk
    let e_ext := modPKEExtendError (NegacyclicPoly (Zq params) N) k e1 e2
    let wit : ModZKPSecretWitness (NegacyclicPoly (Zq params) N) k (k + 1) := { s := r, e := e_ext }
    let pub : ModZKPPublicInfo (NegacyclicPoly (Zq params) N) k (k + 1) :=
      { A := M_enc, t := modPKECiphertextTarget (NegacyclicPoly (Zq params) N) k ct delta_m }
    let w := modZkpCommit (NegacyclicPoly (Zq params) N) k (k + 1) M_enc y_r y_e
    let resp := modZkpRespond (NegacyclicPoly (Zq params) N) k (k + 1) y_r y_e c wit
    modZkpVerifyAlgebraic (NegacyclicPoly (Zq params) N) k (k + 1) pub c w resp ∧
    modZkpVerifyBound (NegacyclicPoly (Zq params) N) k (k + 1) resp safe_bound := by
  intro ct M_enc e_ext wit pub w resp
  constructor
  · have h_pub_eq :
        pub = mkModZKPPublicInfo (NegacyclicPoly (Zq params) N) k (k + 1) M_enc wit := by
      dsimp [pub, mkModZKPPublicInfo, wit, M_enc, e_ext, ct]
      rw [modPKE_ciphertext_relation_correct (NegacyclicPoly (Zq params) N) k pk r e1 e2 delta_m]
    rw [h_pub_eq]
    exact mod_zkp_completeness (NegacyclicPoly (Zq params) N) k (k + 1) M_enc y_r y_e c wit
  · have he_ext : ∀ i : Fin (k + 1), normInf params (e_ext i).coeffs ≤ 1 := by
      intro i
      refine Fin.lastCases ?_ ?_ i
      · dsimp [e_ext, modPKEExtendError]
        rw [Fin.snoc_last]
        exact he2
      · intro j
        dsimp [e_ext, modPKEExtendError]
        rw [Fin.snoc_castSucc]
        exact he1 j
    exact concrete_mod_zkp_respond_passes_verify k (k + 1) params N safe_bound beta 1
      y_r y_e c wit hc hr he_ext hbeta h_yr h_ye

lemma normInf_finset_sum_poly_le {ι : Type*}
    (params : LWEParams) (N : ℕ) (s : Finset ι)
    (f : ι → NegacyclicPoly (Zq params) N) :
    normInf params (∑ i ∈ s, f i).coeffs ≤ ∑ i ∈ s, normInf params (f i).coeffs := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    unfold normInf
    rw [Finset.sup_le_iff]
    intro j _
    change norm params 0 ≤ 0
    unfold norm centeredLift
    rw [ZMod.val_zero]
    dsimp
    split_ifs <;> omega
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have h_add := norm_add_le params (f a).coeffs (∑ i ∈ s, f i).coeffs
    change normInf params ((f a).coeffs + (∑ i ∈ s, f i).coeffs) ≤ _
    omega

theorem dotProductR_ternary_norm_le (params : LWEParams) (k N : ℕ) [Fact (0 < N)]
    (u v : VectorR (NegacyclicPoly (Zq params) N) k)
    (hu : ∀ i : Fin k, NegacyclicPoly.IsTernaryPoly (u i))
    (hv : ∀ i : Fin k, normInf params (v i).coeffs ≤ 1) :
    normInf params (dotProductR (NegacyclicPoly (Zq params) N) k u v).coeffs ≤ k * N := by
  dsimp [dotProductR]
  have h_sum := normInf_finset_sum_poly_le params N Finset.univ (fun i : Fin k => u i * v i)
  have h_each : ∀ i ∈ (Finset.univ : Finset (Fin k)),
      normInf params (u i * v i).coeffs ≤ N := by
    intro i _
    have h_mul := NegacyclicPoly.normInf_ternary_mul_le params N (u i) (v i) (hu i)
    have h_v := hv i
    have h_le : N * normInf params (v i).coeffs ≤ N * 1 := Nat.mul_le_mul_left N h_v
    omega
  have h_bound := Finset.sum_le_sum h_each
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h_bound
  omega

theorem modPKE_ternary_noise_bound (params : LWEParams) (k N : ℕ) [Fact (0 < N)]
    (s e r e1 : VectorR (NegacyclicPoly (Zq params) N) k)
    (e2 : NegacyclicPoly (Zq params) N)
    (hr_tern : ∀ i : Fin k, NegacyclicPoly.IsTernaryPoly (r i))
    (hs_tern : ∀ i : Fin k, NegacyclicPoly.IsTernaryPoly (s i))
    (he_norm : ∀ i : Fin k, normInf params (e i).coeffs ≤ 1)
    (he1_norm : ∀ i : Fin k, normInf params (e1 i).coeffs ≤ 1)
    (he2_norm : normInf params e2.coeffs ≤ 1) :
    normInf params
      (dotProductR (NegacyclicPoly (Zq params) N) k e r + e2 -
        dotProductR (NegacyclicPoly (Zq params) N) k s e1).coeffs ≤ 2 * k * N + 1 := by
  have h_comm :
      dotProductR (NegacyclicPoly (Zq params) N) k e r =
        dotProductR (NegacyclicPoly (Zq params) N) k r e := by
    dsimp [dotProductR]
    apply Finset.sum_congr rfl
    intro i _
    rw [mul_comm]
  rw [h_comm]
  have h_re := dotProductR_ternary_norm_le params k N r e hr_tern he_norm
  have h_se1 := dotProductR_ternary_norm_le params k N s e1 hs_tern he1_norm
  have h_sub :
      normInf params
        (dotProductR (NegacyclicPoly (Zq params) N) k r e + e2 -
          dotProductR (NegacyclicPoly (Zq params) N) k s e1).coeffs ≤
      normInf params (dotProductR (NegacyclicPoly (Zq params) N) k r e + e2).coeffs +
        normInf params (dotProductR (NegacyclicPoly (Zq params) N) k s e1).coeffs :=
    norm_sub_le params
      (dotProductR (NegacyclicPoly (Zq params) N) k r e + e2).coeffs
      (dotProductR (NegacyclicPoly (Zq params) N) k s e1).coeffs
  have h_add :
      normInf params (dotProductR (NegacyclicPoly (Zq params) N) k r e + e2).coeffs ≤
        normInf params (dotProductR (NegacyclicPoly (Zq params) N) k r e).coeffs +
          normInf params e2.coeffs :=
    norm_add_le params
      (dotProductR (NegacyclicPoly (Zq params) N) k r e).coeffs
      e2.coeffs
  have h_2kn : 2 * k * N = k * N + k * N := by ring
  omega

theorem modKEM_zero_failure_correctness {Key Coins Seed : Type*}
    (params : LWEParams) (k N Δ t : ℕ) [Fact (0 < N)]
    [DecidableEq (ModPKECiphertext (NegacyclicPoly (Zq params) N) k)]
    (G : ModPKEPublicKey (NegacyclicPoly (Zq params) N) k → (Fin N → ℕ) → Key × Coins)
    (expandR : Coins → VectorR (NegacyclicPoly (Zq params) N) k)
    (expandE1 : Coins → VectorR (NegacyclicPoly (Zq params) N) k)
    (expandE2 : Coins → NegacyclicPoly (Zq params) N)
    (J : Seed → ModPKECiphertext (NegacyclicPoly (Zq params) N) k → Key)
    (A : MatrixR (NegacyclicPoly (Zq params) N) k k)
    (s e : VectorR (NegacyclicPoly (Zq params) N) k)
    (z : Seed)
    (m : Fin N → ℕ)
    (ht_le : Δ * t ≤ params.q)
    (hm : ∀ idx : Fin N, m idx < t)
    (hs_tern : ∀ i : Fin k, NegacyclicPoly.IsTernaryPoly (s i))
    (he_norm : ∀ i : Fin k, normInf params (e i).coeffs ≤ 1)
    (hr_tern : ∀ c : Coins, ∀ i : Fin k, NegacyclicPoly.IsTernaryPoly (expandR c i))
    (he1_norm : ∀ c : Coins, ∀ i : Fin k, normInf params (expandE1 c i).coeffs ≤ 1)
    (he2_norm : ∀ c : Coins, normInf params (expandE2 c).coeffs ≤ 1)
    (h_zero_fail : 2 * (2 * k * N + 1) < Δ) :
    let pk := modPKEKeygen (NegacyclicPoly (Zq params) N) k A s e
    let enc := modKEMEncaps params k N Δ G expandR expandE1 expandE2 pk m
    modKEMDecaps params k N Δ G expandR expandE1 expandE2 J pk s z enc.1 = enc.2 := by
  intro pk enc
  apply modKEM_correctness params k N Δ t G expandR expandE1 expandE2 J A s e z m ht_le hm
  dsimp
  set coins := (G (modPKEKeygen (NegacyclicPoly (Zq params) N) k A s e) m).2
  have h_bound := modPKE_ternary_noise_bound params k N s e
    (expandR coins) (expandE1 coins) (expandE2 coins)
    (hr_tern coins) hs_tern he_norm (he1_norm coins) (he2_norm coins)
  omega

end ModulePKE

section BFVModSwitchAndGalois

open scoped BigOperators

def bfvModSwitchCoeff (q q_new c : ℕ) : ℕ :=
  (q_new * c + q / 2) / q

def bfvModSwitchRem (q q_new c : ℕ) : ℕ :=
  (q_new * c + q / 2) % q

theorem bfvModSwitchCoeff_eq (q q_new c : ℕ) :
    q * bfvModSwitchCoeff q q_new c + bfvModSwitchRem q q_new c = q_new * c + q / 2 := by
  dsimp [bfvModSwitchCoeff, bfvModSwitchRem]
  exact Nat.div_add_mod (q_new * c + q / 2) q

theorem bfvModSwitchRem_lt (q q_new c : ℕ) (hq : 0 < q) :
    bfvModSwitchRem q q_new c < q := by
  dsimp [bfvModSwitchRem]
  exact Nat.mod_lt (q_new * c + q / 2) hq

theorem bfvModSwitch_error_bound (q q_new c : ℕ) (hq : 0 < q) :
    -((q - 1 - q / 2 : ℕ) : ℤ) ≤
      (q : ℤ) * (bfvModSwitchCoeff q q_new c : ℤ) - (q_new : ℤ) * (c : ℤ) ∧
    (q : ℤ) * (bfvModSwitchCoeff q q_new c : ℤ) - (q_new : ℤ) * (c : ℤ) ≤
      ((q / 2 : ℕ) : ℤ) := by
  have h_eq := bfvModSwitchCoeff_eq q q_new c
  have h_lt := bfvModSwitchRem_lt q q_new c hq
  omega

structure GaloisKey (R : Type*) (l : ℕ) where
  a_gk : VectorR R l
  b_gk : VectorR R l

def mkBFVGaloisKey (R : Type*) [CommRing R] {l : ℕ}
    (σ : R →+* R) (a_gk e_gk : VectorR R l) (s : R) (G : VectorR R l) : GaloisKey R l :=
  { a_gk := a_gk,
    b_gk := fun i => -(a_gk i * s + e_gk i) + G i * σ s }

def bfvApplyGalois (R : Type*) [CommRing R] {l : ℕ}
    (σ : R →+* R) (ct : BFVCiphertext R) (decomp : R → VectorR R l)
    (gk : GaloisKey R l) : BFVCiphertext R :=
  let c1_dec := decomp (σ ct.c1)
  { c0 := σ ct.c0 + (∑ i, c1_dec i * gk.b_gk i),
    c1 := ∑ i, c1_dec i * gk.a_gk i }

theorem bfvApplyGalois_phase (R : Type*) [CommRing R] {l : ℕ}
    (σ : R →+* R) (ct : BFVCiphertext R) (s : R)
    (a_gk e_gk G : VectorR R l) (decomp : R → VectorR R l)
    (h_dec : IsValidDecomposition G decomp) :
    let gk := mkBFVGaloisKey R σ a_gk e_gk s G
    bfvPhase R (bfvApplyGalois R σ ct decomp gk) s =
      σ (bfvPhase R ct s) - (∑ i, decomp (σ ct.c1) i * e_gk i) := by
  dsimp [mkBFVGaloisKey, bfvApplyGalois, bfvPhase]
  rw [map_add, map_mul]
  simp only [sub_eq_add_neg, neg_add, mul_add, mul_neg, Finset.sum_add_distrib,
    Finset.sum_neg_distrib]
  have h1 : (∑ i : Fin l, decomp (σ ct.c1) i * (a_gk i * s)) =
      (∑ i : Fin l, decomp (σ ct.c1) i * a_gk i) * s := by
    simp_rw [← mul_assoc, Finset.sum_mul]
  have h2 : (∑ i : Fin l, decomp (σ ct.c1) i * (G i * σ s)) =
      (∑ i : Fin l, decomp (σ ct.c1) i * G i) * σ s := by
    simp_rw [← mul_assoc, Finset.sum_mul]
  rw [h1, h2, h_dec (σ ct.c1)]
  ring

theorem bfvNoise_applyGalois (R : Type*) [CommRing R] {l : ℕ}
    (σ : R →+* R) (ct : BFVCiphertext R) (s dm : R)
    (a_gk e_gk G : VectorR R l) (decomp : R → VectorR R l)
    (h_dec : IsValidDecomposition G decomp) :
    let gk := mkBFVGaloisKey R σ a_gk e_gk s G
    bfvNoise R (bfvApplyGalois R σ ct decomp gk) s (σ dm) =
      σ (bfvNoise R ct s dm) - (∑ i, decomp (σ ct.c1) i * e_gk i) := by
  dsimp [bfvNoise]
  rw [bfvApplyGalois_phase R σ ct s a_gk e_gk G decomp h_dec, map_sub]
  ring

theorem bfvDecryptPoly_applyGalois_correct (params : LWEParams) (N Δ t : ℕ) {l : ℕ} [Fact (0 < N)]
    (σ : NegacyclicPoly (Zq params) N →+* NegacyclicPoly (Zq params) N)
    (ct : BFVCiphertext (NegacyclicPoly (Zq params) N))
    (s E : NegacyclicPoly (Zq params) N)
    (a_gk e_gk G : VectorR (NegacyclicPoly (Zq params) N) l)
    (decomp : NegacyclicPoly (Zq params) N → VectorR (NegacyclicPoly (Zq params) N) l)
    (m m_gal : Fin N → ℕ)
    (h_dec : IsValidDecomposition G decomp)
    (ht_le : Δ * t ≤ params.q)
    (hm : ∀ k : Fin N, m_gal k < t)
    (h_phase : bfvPhase (NegacyclicPoly (Zq params) N) ct s = bfvEncodePoly params N Δ m + E)
    (h_encode_gal : σ (bfvEncodePoly params N Δ m) = bfvEncodePoly params N Δ m_gal)
    (h_noise : 2 * normInf params
      (σ E - (∑ i, decomp (σ ct.c1) i * e_gk i)).coeffs < Δ) :
    let gk := mkBFVGaloisKey (NegacyclicPoly (Zq params) N) σ a_gk e_gk s G
    bfvDecryptPoly params N Δ s
      (bfvApplyGalois (NegacyclicPoly (Zq params) N) σ ct decomp gk) = m_gal := by
  intro gk
  have h_phase_gal :
      bfvPhase (NegacyclicPoly (Zq params) N)
        (bfvApplyGalois (NegacyclicPoly (Zq params) N) σ ct decomp gk) s =
        bfvEncodePoly params N Δ m_gal +
          (σ E - (∑ i, decomp (σ ct.c1) i * e_gk i)) := by
    rw [bfvApplyGalois_phase (NegacyclicPoly (Zq params) N) σ ct s a_gk e_gk G decomp h_dec,
      h_phase, map_add, h_encode_gal]
    ring
  exact bfvDecryptPoly_of_phase_eq params N Δ t s
    (σ E - (∑ i, decomp (σ ct.c1) i * e_gk i))
    (bfvApplyGalois (NegacyclicPoly (Zq params) N) σ ct decomp gk)
    m_gal ht_le hm h_phase_gal h_noise

end BFVModSwitchAndGalois

section StandardLWERegev

open scoped BigOperators

def samplePhase (R : Type*) [CommRing R] {n m : ℕ}
    (c : Sample R n m) (s : VectorR R n) : VectorR R m :=
  fun i => c.b i - ∑ j : Fin n, c.A i j * s j

def regevEncrypt (params : LWEParams) (Δ : ℕ)
    (base : Sample (Zq params) params.n params.m) (msg : Fin params.m → ℕ) :
    Sample (Zq params) params.n params.m :=
  { A := base.A,
    b := fun i => base.b i + bfvEncodeElem params Δ (msg i) }

def regevDecrypt (params : LWEParams) (Δ : ℕ)
    (s : VectorR (Zq params) params.n)
    (ct : Sample (Zq params) params.n params.m) : Fin params.m → ℕ :=
  fun i => bfvDecodeElem params Δ (samplePhase (Zq params) ct s i)

theorem regevPhase_eq (params : LWEParams) (Δ : ℕ)
    (A : MatrixR (Zq params) params.n params.m)
    (s : VectorR (Zq params) params.n)
    (e : VectorR (Zq params) params.m)
    (msg : Fin params.m → ℕ) (i : Fin params.m) :
    samplePhase (Zq params)
      (regevEncrypt params Δ (mkSample (Zq params) params.n params.m A s e) msg) s i =
      bfvEncodeElem params Δ (msg i) + e i := by
  dsimp [samplePhase, regevEncrypt, mkSample, evaluate]
  ring

theorem regevDecrypt_correct (params : LWEParams) (Δ t : ℕ)
    (A : MatrixR (Zq params) params.n params.m)
    (s : VectorR (Zq params) params.n)
    (e : VectorR (Zq params) params.m)
    (msg : Fin params.m → ℕ)
    (ht_le : Δ * t ≤ params.q)
    (hm : ∀ i : Fin params.m, msg i < t)
    (h_noise : 2 * normInf params e < Δ) :
    regevDecrypt params Δ s
      (regevEncrypt params Δ (mkSample (Zq params) params.n params.m A s e) msg) = msg := by
  ext i
  unfold regevDecrypt
  rw [regevPhase_eq]
  have hi_le : norm params (e i) ≤ normInf params e :=
    Finset.le_sup (f := fun j => norm params (e j)) (Finset.mem_univ i)
  have hi_noise : 2 * norm params (e i) < Δ := by omega
  exact bfvDecodeElem_correct params Δ t (msg i) (e i) ht_le (hm i) hi_noise

theorem regevDecrypt_add_correct (params : LWEParams) (Δ t : ℕ)
    (A1 A2 : MatrixR (Zq params) params.n params.m)
    (s : VectorR (Zq params) params.n)
    (e1 e2 : VectorR (Zq params) params.m)
    (msg1 msg2 : Fin params.m → ℕ)
    (ht_le : Δ * t ≤ params.q)
    (hm : ∀ i : Fin params.m, msg1 i + msg2 i < t)
    (h_noise : 2 * (normInf params e1 + normInf params e2) < Δ) :
    let ct1 := regevEncrypt params Δ (mkSample (Zq params) params.n params.m A1 s e1) msg1
    let ct2 := regevEncrypt params Δ (mkSample (Zq params) params.n params.m A2 s e2) msg2
    regevDecrypt params Δ s (addSamples (Zq params) ct1 ct2) =
      fun i => msg1 i + msg2 i := by
  intro ct1 ct2
  ext i
  unfold regevDecrypt
  have h_phase_sum :
      samplePhase (Zq params) (addSamples (Zq params) ct1 ct2) s i =
        bfvEncodeElem params Δ (msg1 i + msg2 i) + (e1 + e2) i := by
    dsimp [samplePhase, addSamples, ct1, ct2, regevEncrypt, mkSample, evaluate, bfvEncodeElem]
    push_cast
    simp only [add_mul, Finset.sum_add_distrib]
    ring
  rw [h_phase_sum]
  have h_tri := norm_add_le params e1 e2
  have hi_le : norm params ((e1 + e2) i) ≤ normInf params (e1 + e2) :=
    Finset.le_sup (f := fun j => norm params ((e1 + e2) j)) (Finset.mem_univ i)
  have hi_noise : 2 * norm params ((e1 + e2) i) < Δ := by omega
  exact bfvDecodeElem_correct params Δ t (msg1 i + msg2 i) ((e1 + e2) i) ht_le (hm i) hi_noise

end StandardLWERegev

section BFVBatchSIMD

open scoped BigOperators

def bfvBatchEncode {Rt : Type*} [CommRing Rt] {N : ℕ}
    (ψ_inv n_inv : Rt) (slots : Fin N → Rt) : NegacyclicPoly Rt N :=
  concreteInvNTT ψ_inv n_inv slots

def bfvBatchDecode {Rt : Type*} [CommRing Rt] {N : ℕ}
    (ψ : Rt) (pt : NegacyclicPoly Rt N) : Fin N → Rt :=
  concreteNTT ψ pt

theorem bfvBatchEncode_decode {Rt : Type*} [CommRing Rt] {N : ℕ}
    (ψ ψ_inv n_inv : Rt) (h_orth : IsValidNTTInverse N ψ ψ_inv n_inv)
    (pt : NegacyclicPoly Rt N) :
    bfvBatchEncode ψ_inv n_inv (bfvBatchDecode ψ pt) = pt :=
  concreteInvNTT_concreteNTT ψ ψ_inv n_inv h_orth pt

theorem bfvBatchDecode_add {Rt : Type*} [CommRing Rt] {N : ℕ}
    (ψ : Rt) (p1 p2 : NegacyclicPoly Rt N) :
    bfvBatchDecode ψ (p1 + p2) = bfvBatchDecode ψ p1 + bfvBatchDecode ψ p2 :=
  concreteNTT_map_add ψ p1 p2

theorem bfvBatchDecode_mul {Rt : Type*} [CommRing Rt] {N : ℕ} [Fact (0 < N)]
    (ψ : Rt) (hpsi : ψ ^ N = -1) (p1 p2 : NegacyclicPoly Rt N) :
    bfvBatchDecode ψ (p1 * p2) = bfvBatchDecode ψ p1 * bfvBatchDecode ψ p2 :=
  concreteNTT_map_mul ψ hpsi p1 p2

end BFVBatchSIMD

section CompressedModPKE

open scoped BigOperators

structure ModPKECompressedPublicKey (Seed R : Type*) (k : ℕ) where
  rho : Seed
  t : VectorR R k

def modPKEKeygenCompressed {Seed : Type*} (R : Type*) [CommRing R] (k : ℕ)
    (expandA : Seed → MatrixR R k k) (rho : Seed) (s e : VectorR R k) :
    ModPKECompressedPublicKey Seed R k :=
  { rho := rho,
    t := evaluate R k k (expandA rho) s e }

def modPKEDecompressPublicKey {Seed : Type*} (R : Type*) (k : ℕ)
    (expandA : Seed → MatrixR R k k) (cpk : ModPKECompressedPublicKey Seed R k) :
    ModPKEPublicKey R k :=
  { A := expandA cpk.rho,
    t := cpk.t }

theorem modPKEDecompress_keygenCompressed_eq {Seed : Type*} (R : Type*) [CommRing R] (k : ℕ)
    (expandA : Seed → MatrixR R k k) (rho : Seed) (s e : VectorR R k) :
    modPKEDecompressPublicKey R k expandA (modPKEKeygenCompressed R k expandA rho s e) =
      modPKEKeygen R k (expandA rho) s e :=
  rfl

def lweCompressCoeff (q d x : ℕ) : ℕ :=
  ((x * 2 ^ d + q / 2) / q) % 2 ^ d

def lweDecompressCoeff (q d y : ℕ) : ℕ :=
  (y * q + 2 ^ (d - 1)) / 2 ^ d

theorem lweCompressCoeff_lt (q d x : ℕ) :
    lweCompressCoeff q d x < 2 ^ d := by
  dsimp [lweCompressCoeff]
  exact Nat.mod_lt _ (Nat.pow_pos (by decide))

theorem modPKE_compressed_phase_eq (R : Type*) [CommRing R] (k : ℕ)
    (A : MatrixR R k k) (s e r e1 e_u : VectorR R k) (e2 e_v delta_m : R) :
    let pk := modPKEKeygen R k A s e
    let ct := modPKEEncrypt R k pk r e1 e2 delta_m
    let ct_comp : ModPKECiphertext R k := { u := ct.u + e_u, v := ct.v + e_v }
    modPKEPhase R k ct_comp s =
      delta_m +
        ((dotProductR R k e r + e2 - dotProductR R k s e1) +
          (e_v - dotProductR R k s e_u)) := by
  intro pk ct ct_comp
  have h_base := modPKE_phase_eq R k A s e r e1 e2 delta_m
  have h_su :
      dotProductR R k s (ct.u + e_u) =
        dotProductR R k s ct.u + dotProductR R k s e_u := by
    dsimp [dotProductR]
    simp only [mul_add, Finset.sum_add_distrib]
  change (ct.v + e_v) - dotProductR R k s (ct.u + e_u) = _
  rw [h_su]
  have h_expand :
      (ct.v + e_v) - (dotProductR R k s ct.u + dotProductR R k s e_u) =
        modPKEPhase R k ct s + (e_v - dotProductR R k s e_u) := by
    dsimp [modPKEPhase]
    ring
  rw [h_expand, h_base]
  ring

theorem modPKE_compressed_decrypt_correct (params : LWEParams) (k N Δ t : ℕ) [Fact (0 < N)]
    (A : MatrixR (NegacyclicPoly (Zq params) N) k k)
    (s e r e1 e_u : VectorR (NegacyclicPoly (Zq params) N) k)
    (e2 e_v : NegacyclicPoly (Zq params) N)
    (m : Fin N → ℕ)
    (ht_le : Δ * t ≤ params.q)
    (hm : ∀ idx : Fin N, m idx < t)
    (h_noise : 2 * (normInf params
      (dotProductR (NegacyclicPoly (Zq params) N) k e r + e2 -
        dotProductR (NegacyclicPoly (Zq params) N) k s e1).coeffs +
      normInf params
        (e_v - dotProductR (NegacyclicPoly (Zq params) N) k s e_u).coeffs) < Δ) :
    let pk := modPKEKeygen (NegacyclicPoly (Zq params) N) k A s e
    let ct := modPKEEncrypt (NegacyclicPoly (Zq params) N) k pk r e1 e2 (bfvEncodePoly params N Δ m)
    let ct_comp : ModPKECiphertext (NegacyclicPoly (Zq params) N) k :=
      { u := ct.u + e_u, v := ct.v + e_v }
    bfvDecodePoly params N Δ (modPKEPhase (NegacyclicPoly (Zq params) N) k ct_comp s) = m := by
  intro pk ct ct_comp
  have h_phase := modPKE_compressed_phase_eq (NegacyclicPoly (Zq params) N) k A s e r e1 e_u e2 e_v
    (bfvEncodePoly params N Δ m)
  change bfvDecodePoly params N Δ (modPKEPhase (NegacyclicPoly (Zq params) N) k ct_comp s) = m
  rw [h_phase]
  ext idx
  unfold bfvDecodePoly
  rw [NegacyclicPoly.add_coeffs]
  dsimp [bfvEncodePoly]
  set E_pke := dotProductR (NegacyclicPoly (Zq params) N) k e r + e2 -
    dotProductR (NegacyclicPoly (Zq params) N) k s e1
  set E_comp := e_v - dotProductR (NegacyclicPoly (Zq params) N) k s e_u
  have h_tri := norm_add_le params E_pke.coeffs E_comp.coeffs
  have h_le : norm params ((E_pke + E_comp).coeffs idx) ≤ normInf params (E_pke + E_comp).coeffs :=
    Finset.le_sup (f := fun j => norm params ((E_pke + E_comp).coeffs j)) (Finset.mem_univ idx)
  have h_eq_add : normInf params (E_pke + E_comp).coeffs ≤
      normInf params E_pke.coeffs + normInf params E_comp.coeffs := h_tri
  have h_idx_noise : 2 * norm params ((E_pke + E_comp).coeffs idx) < Δ := by omega
  exact bfvDecodeElem_correct params Δ t (m idx) ((E_pke + E_comp).coeffs idx)
    ht_le (hm idx) h_idx_noise

end CompressedModPKE

section RegevINDCPASecurity

open scoped BigOperators

def regevEncodeVec (params : LWEParams) (Δ : ℕ) (msg : Fin params.m → ℕ) :
    VectorR (Zq params) params.m :=
  fun i => bfvEncodeElem params Δ (msg i)

def regevEncryptPad (params : LWEParams) (Δ : ℕ)
    (A : MatrixR (Zq params) params.n params.m)
    (pad : VectorR (Zq params) params.m)
    (msg : Fin params.m → ℕ) : Sample (Zq params) params.n params.m :=
  { A := A, b := pad + regevEncodeVec params Δ msg }

theorem regevEncrypt_eq_regevEncryptPad (params : LWEParams) (Δ : ℕ)
    (sample : Sample (Zq params) params.n params.m) (msg : Fin params.m → ℕ) :
    regevEncrypt params Δ sample msg = regevEncryptPad params Δ sample.A sample.b msg := by
  cases sample
  rfl

def regevPadEquiv (params : LWEParams) (Δ : ℕ) (msg : Fin params.m → ℕ) :
    VectorR (Zq params) params.m ≃ VectorR (Zq params) params.m :=
  Equiv.addRight (regevEncodeVec params Δ msg)

theorem regevPad_bijective (params : LWEParams) (Δ : ℕ) (msg : Fin params.m → ℕ) :
    Function.Bijective
      (fun pad : VectorR (Zq params) params.m => pad + regevEncodeVec params Δ msg) :=
  (regevPadEquiv params Δ msg).bijective

theorem regevUniformSum_eq (params : LWEParams) [NeZero params.q] (Δ : ℕ)
    {M : Type*} [AddCommMonoid M]
    (D : Sample (Zq params) params.n params.m → M)
    (A : MatrixR (Zq params) params.n params.m)
    (msg : Fin params.m → ℕ) :
    (∑ u : VectorR (Zq params) params.m, D (regevEncryptPad params Δ A u msg)) =
      ∑ v : VectorR (Zq params) params.m, D { A := A, b := v } := by
  exact Equiv.sum_comp (regevPadEquiv params Δ msg) (fun v => D { A := A, b := v })

theorem regevUniformSum_indep (params : LWEParams) [NeZero params.q] (Δ : ℕ)
    {M : Type*} [AddCommMonoid M]
    (D : Sample (Zq params) params.n params.m → M)
    (A : MatrixR (Zq params) params.n params.m)
    (msg0 msg1 : Fin params.m → ℕ) :
    (∑ u : VectorR (Zq params) params.m, D (regevEncryptPad params Δ A u msg0)) =
      (∑ u : VectorR (Zq params) params.m, D (regevEncryptPad params Δ A u msg1)) := by
  rw [regevUniformSum_eq params Δ D A msg0, regevUniformSum_eq params Δ D A msg1]

theorem regev_ind_cpa_reduction (params : LWEParams) [NeZero params.q] (Δ : ℕ)
    (D : Sample (Zq params) params.n params.m → ℤ)
    (A : MatrixR (Zq params) params.n params.m)
    (E_LWE : (VectorR (Zq params) params.m → ℤ) → ℤ)
    (msg0 msg1 : Fin params.m → ℕ) :
    let f0 := fun pad => D (regevEncryptPad params Δ A pad msg0)
    let f1 := fun pad => D (regevEncryptPad params Δ A pad msg1)
    let u0 := ∑ u : VectorR (Zq params) params.m, f0 u
    let u1 := ∑ u : VectorR (Zq params) params.m, f1 u
    (E_LWE f0 - E_LWE f1).natAbs ≤ (E_LWE f0 - u0).natAbs + (E_LWE f1 - u1).natAbs := by
  intro f0 f1 u0 u1
  have h_unif : u0 = u1 := regevUniformSum_indep params Δ D A msg0 msg1
  omega

def bitToInt (b : Bool) : ℤ :=
  if b then 1 else 0

structure FinDist (α : Type*) [Fintype α] where
  weight : α → ℕ

def FinDist.totalMass {α : Type*} [Fintype α] (dist : FinDist α) : ℕ :=
  ∑ x : α, dist.weight x

def uniformFinDist (α : Type*) [Fintype α] : FinDist α :=
  { weight := fun _ => 1 }

def FinDist.acceptWeight {α : Type*} [Fintype α] (dist : FinDist α) (P : α → Bool) : ℤ :=
  ∑ x : α, (dist.weight x : ℤ) * bitToInt (P x)

def FinDist.eventMass {α : Type*} [Fintype α]
    (dist : FinDist α) (E : α → Prop) [DecidablePred E] : ℕ :=
  ∑ x : α, if E x then dist.weight x else 0

theorem FinDist.difference_lemma {α : Type*} [Fintype α]
    (dist : FinDist α) (P1 P2 : α → Bool) (E : α → Prop) [DecidablePred E]
    (h_agree : ∀ x : α, ¬ E x → P1 x = P2 x) :
    (dist.acceptWeight P1 - dist.acceptWeight P2).natAbs ≤ dist.eventMass E := by
  dsimp [FinDist.acceptWeight, FinDist.eventMass]
  rw [← Finset.sum_sub_distrib]
  have h_term : ∀ x : α,
      ((dist.weight x : ℤ) * bitToInt (P1 x) - (dist.weight x : ℤ) * bitToInt (P2 x)).natAbs ≤
        if E x then dist.weight x else 0 := by
    intro x
    by_cases hx : E x
    · rw [if_pos hx]
      dsimp [bitToInt]
      cases P1 x <;> cases P2 x <;> simp
    · rw [if_neg hx, h_agree x hx, sub_self]
      simp
  have h_sum_le :
      (∑ x : α,
        ((dist.weight x : ℤ) * bitToInt (P1 x) -
          (dist.weight x : ℤ) * bitToInt (P2 x))).natAbs ≤
        ∑ x : α,
          ((dist.weight x : ℤ) * bitToInt (P1 x) -
            (dist.weight x : ℤ) * bitToInt (P2 x)).natAbs := by
    induction (Finset.univ : Finset α) using Finset.cons_induction with
    | empty => simp
    | cons a s ha ih =>
      rw [Finset.sum_cons, Finset.sum_cons]
      have h_tri := Int.natAbs_add_le
        ((dist.weight a : ℤ) * bitToInt (P1 a) - (dist.weight a : ℤ) * bitToInt (P2 a))
        (∑ x ∈ s, ((dist.weight x : ℤ) * bitToInt (P1 x) - (dist.weight x : ℤ) * bitToInt (P2 x)))
      omega
  have h_bound :
      (∑ x : α,
        ((dist.weight x : ℤ) * bitToInt (P1 x) -
          (dist.weight x : ℤ) * bitToInt (P2 x)).natAbs) ≤
        ∑ x : α, if E x then dist.weight x else 0 :=
    Finset.sum_le_sum (fun x _ => h_term x)
  omega

def regevShiftedDistinguisher (params : LWEParams) (Δ : ℕ)
    (msg : Fin params.m → ℕ) (D : Sample (Zq params) params.n params.m → Bool) :
    Sample (Zq params) params.n params.m → Bool :=
  fun sample => D (regevEncrypt params Δ sample msg)

def DLWEAdvantage (params : LWEParams) [NeZero params.q]
    (A : MatrixR (Zq params) params.n params.m)
    (seDist : FinDist (VectorR (Zq params) params.n × VectorR (Zq params) params.m))
    (D_dlwe : Sample (Zq params) params.n params.m → Bool) : ℕ :=
  let cardU : ℤ := Fintype.card (VectorR (Zq params) params.m)
  let realW : ℤ := seDist.acceptWeight
    (fun se => D_dlwe (mkSample (Zq params) params.n params.m A se.1 se.2))
  let unifW : ℤ := ∑ u : VectorR (Zq params) params.m, bitToInt (D_dlwe { A := A, b := u })
  (cardU * realW - (seDist.totalMass : ℤ) * unifW).natAbs

def INDCPAAdvantage (params : LWEParams) [NeZero params.q] (Δ : ℕ)
    (A : MatrixR (Zq params) params.n params.m)
    (seDist : FinDist (VectorR (Zq params) params.n × VectorR (Zq params) params.m))
    (msg0 msg1 : Fin params.m → ℕ)
    (D : Sample (Zq params) params.n params.m → Bool) : ℕ :=
  let cardU : ℤ := Fintype.card (VectorR (Zq params) params.m)
  let real0 : ℤ := seDist.acceptWeight
    (fun se => D (regevEncrypt params Δ (mkSample (Zq params) params.n params.m A se.1 se.2) msg0))
  let real1 : ℤ := seDist.acceptWeight
    (fun se => D (regevEncrypt params Δ (mkSample (Zq params) params.n params.m A se.1 se.2) msg1))
  (cardU * real0 - cardU * real1).natAbs

theorem regevShifted_uniform_sum_eq (params : LWEParams) [NeZero params.q] (Δ : ℕ)
    (A : MatrixR (Zq params) params.n params.m)
    (msg : Fin params.m → ℕ)
    (D : Sample (Zq params) params.n params.m → Bool) :
    (∑ u : VectorR (Zq params) params.m,
        bitToInt (regevShiftedDistinguisher params Δ msg D { A := A, b := u })) =
      ∑ v : VectorR (Zq params) params.m, bitToInt (D { A := A, b := v }) := by
  dsimp [regevShiftedDistinguisher]
  have h_pad : ∀ u : VectorR (Zq params) params.m,
      regevEncrypt params Δ { A := A, b := u } msg = regevEncryptPad params Δ A u msg :=
    fun u => regevEncrypt_eq_regevEncryptPad params Δ { A := A, b := u } msg
  simp_rw [h_pad]
  exact regevUniformSum_eq params Δ (fun s => bitToInt (D s)) A msg

theorem regev_ind_cpa_to_dlwe_reduction (params : LWEParams) [NeZero params.q] (Δ : ℕ)
    (A : MatrixR (Zq params) params.n params.m)
    (seDist : FinDist (VectorR (Zq params) params.n × VectorR (Zq params) params.m))
    (msg0 msg1 : Fin params.m → ℕ)
    (D : Sample (Zq params) params.n params.m → Bool) :
    INDCPAAdvantage params Δ A seDist msg0 msg1 D ≤
      DLWEAdvantage params A seDist (regevShiftedDistinguisher params Δ msg0 D) +
        DLWEAdvantage params A seDist (regevShiftedDistinguisher params Δ msg1 D) := by
  dsimp [INDCPAAdvantage, DLWEAdvantage]
  have h0 := regevShifted_uniform_sum_eq params Δ A msg0 D
  have h1 := regevShifted_uniform_sum_eq params Δ A msg1 D
  rw [h0, h1]
  dsimp [regevShiftedDistinguisher]
  omega

end RegevINDCPASecurity

section FujisakiOkamotoINDCCA2Reduction

open scoped BigOperators

def foEncDet {PK Msg Coins Key CT : Type*}
    (encPKE : PK → Msg → Coins → CT)
    (G : PK → Msg → Key × Coins)
    (pk : PK) (m : Msg) : CT :=
  encPKE pk m (G pk m).2

def IsCorrectFOPKE {PK SK Msg Coins Key CT : Type*}
    (encPKE : PK → Msg → Coins → CT)
    (decPKE : SK → CT → Msg)
    (G : PK → Msg → Key × Coins)
    (pk : PK) (sk : SK) : Prop :=
  ∀ m : Msg, decPKE sk (foEncDet encPKE G pk m) = m

theorem foEncDet_injective_of_correct {PK SK Msg Coins Key CT : Type*}
    (encPKE : PK → Msg → Coins → CT)
    (decPKE : SK → CT → Msg)
    (G : PK → Msg → Key × Coins)
    (pk : PK) (sk : SK)
    (h_corr : IsCorrectFOPKE encPKE decPKE G pk sk) :
    Function.Injective (foEncDet encPKE G pk) := by
  intro m1 m2 h_eq
  have h1 := h_corr m1
  have h2 := h_corr m2
  rw [h_eq] at h1
  exact h1.symm.trans h2

theorem foDecPKE_eq_of_foEncDet_eq {PK SK Msg Coins Key CT : Type*}
    (encPKE : PK → Msg → Coins → CT)
    (decPKE : SK → CT → Msg)
    (G : PK → Msg → Key × Coins)
    (pk : PK) (sk : SK)
    (h_corr : IsCorrectFOPKE encPKE decPKE G pk sk)
    {m : Msg} {ct : CT}
    (h_enc : foEncDet encPKE G pk m = ct) :
    decPKE sk ct = m := by
  rw [← h_enc]
  exact h_corr m

def foDecapsReal {PK SK Msg Coins Key Seed CT : Type*} [DecidableEq CT]
    (encPKE : PK → Msg → Coins → CT)
    (decPKE : SK → CT → Msg)
    (G : PK → Msg → Key × Coins)
    (J : Seed → CT → Key)
    (pk : PK) (sk : SK) (z : Seed) (ct : CT) : Key :=
  let m' := decPKE sk ct
  if foEncDet encPKE G pk m' = ct then
    (G pk m').1
  else
    J z ct

def foDecapsSim {PK SK Msg Coins Key Seed CT : Type*} [DecidableEq CT] [DecidableEq Msg]
    (encPKE : PK → Msg → Coins → CT)
    (decPKE : SK → CT → Msg)
    (G : PK → Msg → Key × Coins)
    (J : Seed → CT → Key)
    (Q_G : Finset Msg)
    (pk : PK) (sk : SK) (z : Seed) (ct : CT) : Key :=
  let m' := decPKE sk ct
  if m' ∈ Q_G ∧ foEncDet encPKE G pk m' = ct then
    (G pk m').1
  else
    J z ct

theorem foDecapsSim_accept_iff_mem_image {PK SK Msg Coins Key CT : Type*}
    (encPKE : PK → Msg → Coins → CT)
    (decPKE : SK → CT → Msg)
    (G : PK → Msg → Key × Coins)
    (Q_G : Finset Msg)
    (pk : PK) (sk : SK)
    (h_corr : IsCorrectFOPKE encPKE decPKE G pk sk)
    (ct : CT) :
    (decPKE sk ct ∈ Q_G ∧ foEncDet encPKE G pk (decPKE sk ct) = ct) ↔
      ∃ m ∈ Q_G, foEncDet encPKE G pk m = ct := by
  constructor
  · rintro ⟨hm_in, h_enc⟩
    exact ⟨decPKE sk ct, hm_in, h_enc⟩
  · rintro ⟨m, hm_in, h_enc⟩
    have hm_eq := foDecPKE_eq_of_foEncDet_eq encPKE decPKE G pk sk h_corr h_enc
    rw [hm_eq]
    exact ⟨hm_in, h_enc⟩

def foBadDecapsEvent {PK SK Msg Coins Key CT : Type*}
    (encPKE : PK → Msg → Coins → CT)
    (decPKE : SK → CT → Msg)
    (G : PK → Msg → Key × Coins)
    (Q_G : Finset Msg)
    (pk : PK) (sk : SK) (ct : CT) : Prop :=
  decPKE sk ct ∉ Q_G ∧ foEncDet encPKE G pk (decPKE sk ct) = ct

instance {PK SK Msg Coins Key CT : Type*} [DecidableEq CT] [DecidableEq Msg]
    (encPKE : PK → Msg → Coins → CT)
    (decPKE : SK → CT → Msg)
    (G : PK → Msg → Key × Coins)
    (Q_G : Finset Msg)
    (pk : PK) (sk : SK) :
    DecidablePred (foBadDecapsEvent encPKE decPKE G Q_G pk sk) := by
  intro ct
  unfold foBadDecapsEvent
  infer_instance

theorem foDecapsReal_eq_foDecapsSim_of_not_bad {PK SK Msg Coins Key Seed CT : Type*}
    [DecidableEq CT] [DecidableEq Msg]
    (encPKE : PK → Msg → Coins → CT)
    (decPKE : SK → CT → Msg)
    (G : PK → Msg → Key × Coins)
    (J : Seed → CT → Key)
    (Q_G : Finset Msg)
    (pk : PK) (sk : SK) (z : Seed) (ct : CT)
    (h_not_bad : ¬ foBadDecapsEvent encPKE decPKE G Q_G pk sk ct) :
    foDecapsReal encPKE decPKE G J pk sk z ct =
      foDecapsSim encPKE decPKE G J Q_G pk sk z ct := by
  dsimp [foDecapsReal, foDecapsSim]
  by_cases h_enc : foEncDet encPKE G pk (decPKE sk ct) = ct
  · have hm_in : decPKE sk ct ∈ Q_G := by
      by_contra h_notin
      exact h_not_bad ⟨h_notin, h_enc⟩
    rw [if_pos h_enc, if_pos ⟨hm_in, h_enc⟩]
  · have h_not_both : ¬ (decPKE sk ct ∈ Q_G ∧ foEncDet encPKE G pk (decPKE sk ct) = ct) :=
      fun h => h_enc h.2
    rw [if_neg h_enc, if_neg h_not_both]

theorem foDecapsTranscript_eq_of_no_bad {PK SK Msg Coins Key Seed CT : Type*}
    [DecidableEq CT] [DecidableEq Msg] {q_D : ℕ}
    (encPKE : PK → Msg → Coins → CT)
    (decPKE : SK → CT → Msg)
    (G : PK → Msg → Key × Coins)
    (J : Seed → CT → Key)
    (Q_G : Finset Msg)
    (pk : PK) (sk : SK) (z : Seed)
    (ct_queries : Fin q_D → CT)
    (h_no_bad : ∀ i : Fin q_D, ¬ foBadDecapsEvent encPKE decPKE G Q_G pk sk (ct_queries i)) :
    (fun i => foDecapsReal encPKE decPKE G J pk sk z (ct_queries i)) =
      (fun i => foDecapsSim encPKE decPKE G J Q_G pk sk z (ct_queries i)) := by
  ext i
  exact foDecapsReal_eq_foDecapsSim_of_not_bad encPKE decPKE G J Q_G pk sk z
    (ct_queries i) (h_no_bad i)

theorem fo_ind_cca2_security_reduction {Ω : Type*} [Fintype Ω]
    (dist : FinDist Ω)
    (RealGame0 RealGame1 SimGame0 SimGame1 IdealGame0 IdealGame1 : Ω → Bool)
    (BadDecaps QueryChallenge : Ω → Prop)
    [DecidablePred BadDecaps] [DecidablePred QueryChallenge]
    (h_hop1_b0 : ∀ ω : Ω, ¬ BadDecaps ω → RealGame0 ω = SimGame0 ω)
    (h_hop1_b1 : ∀ ω : Ω, ¬ BadDecaps ω → RealGame1 ω = SimGame1 ω)
    (h_hop2_b0 : ∀ ω : Ω, ¬ QueryChallenge ω → SimGame0 ω = IdealGame0 ω)
    (h_hop2_b1 : ∀ ω : Ω, ¬ QueryChallenge ω → SimGame1 ω = IdealGame1 ω)
    (h_ideal_eq : dist.acceptWeight IdealGame0 = dist.acceptWeight IdealGame1) :
    (dist.acceptWeight RealGame0 - dist.acceptWeight RealGame1).natAbs ≤
      2 * dist.eventMass BadDecaps + 2 * dist.eventMass QueryChallenge := by
  have h_diff_b0 := FinDist.difference_lemma dist RealGame0 SimGame0 BadDecaps h_hop1_b0
  have h_diff_b1 := FinDist.difference_lemma dist RealGame1 SimGame1 BadDecaps h_hop1_b1
  have h_diff_q0 := FinDist.difference_lemma dist SimGame0 IdealGame0 QueryChallenge h_hop2_b0
  have h_diff_q1 := FinDist.difference_lemma dist SimGame1 IdealGame1 QueryChallenge h_hop2_b1
  omega

def foReprogramKey {PK Msg Coins Key : Type*} [DecidableEq Msg]
    (G : PK → Msg → Key × Coins) (m_star : Msg) (k_new : Key) : PK → Msg → Key × Coins :=
  fun pk m => if m = m_star then (k_new, (G pk m).2) else G pk m

theorem foEncDet_reprogramKey_eq {PK Msg Coins Key CT : Type*} [DecidableEq Msg]
    (encPKE : PK → Msg → Coins → CT)
    (G : PK → Msg → Key × Coins) (m_star : Msg) (k_new : Key) (pk : PK) (m : Msg) :
    foEncDet encPKE (foReprogramKey G m_star k_new) pk m = foEncDet encPKE G pk m := by
  dsimp [foEncDet, foReprogramKey]
  split_ifs <;> rfl

theorem foDecapsSim_reprogramKey_eq_of_not_mem {PK SK Msg Coins Key Seed CT : Type*}
    [DecidableEq CT] [DecidableEq Msg]
    (encPKE : PK → Msg → Coins → CT)
    (decPKE : SK → CT → Msg)
    (G : PK → Msg → Key × Coins)
    (J : Seed → CT → Key)
    (Q_G : Finset Msg)
    (m_star : Msg) (k_new : Key)
    (pk : PK) (sk : SK) (z : Seed) (ct : CT)
    (h_not_mem : m_star ∉ Q_G) :
    foDecapsSim encPKE decPKE (foReprogramKey G m_star k_new) J Q_G pk sk z ct =
      foDecapsSim encPKE decPKE G J Q_G pk sk z ct := by
  dsimp [foDecapsSim]
  rw [foEncDet_reprogramKey_eq]
  by_cases h_cond : decPKE sk ct ∈ Q_G ∧ foEncDet encPKE G pk (decPKE sk ct) = ct
  · rw [if_pos h_cond, if_pos h_cond]
    have h_ne : decPKE sk ct ≠ m_star := by
      intro h_eq
      rw [h_eq] at h_cond
      exact h_not_mem h_cond.1
    dsimp [foReprogramKey]
    rw [if_neg h_ne]
  · rw [if_neg h_cond, if_neg h_cond]

theorem fo_concrete_ind_cca2_reduction
    {PK SK Msg Coins Key Seed CT : Type*}
    [Fintype Msg] [Fintype Key] [DecidableEq CT] [DecidableEq Msg] {q_D : ℕ}
    (encPKE : PK → Msg → Coins → CT)
    (decPKE : SK → CT → Msg)
    (G : PK → Msg → Key × Coins)
    (J : Seed → CT → Key)
    (pk : PK) (sk : SK) (z : Seed)
    (Q_G : Msg → Finset Msg)
    (ct_queries : Msg → Fin q_D → CT)
    (adv : CT → Key → (Fin q_D → Key) → Bool) :
    let Ω := Msg × (Key × Key)
    let dist : FinDist Ω := uniformFinDist Ω
    let Real0 : Ω → Bool := fun ω =>
      let m_star := ω.1
      let k0 := ω.2.1
      let G' := foReprogramKey G m_star k0
      let ct_star := foEncDet encPKE G' pk m_star
      adv ct_star k0 (fun i => foDecapsReal encPKE decPKE G' J pk sk z (ct_queries m_star i))
    let Real1 : Ω → Bool := fun ω =>
      let m_star := ω.1
      let k0 := ω.2.1
      let k1 := ω.2.2
      let G' := foReprogramKey G m_star k0
      let ct_star := foEncDet encPKE G' pk m_star
      adv ct_star k1 (fun i => foDecapsReal encPKE decPKE G' J pk sk z (ct_queries m_star i))
    let BadDecaps : Ω → Prop := fun ω =>
      ∃ i : Fin q_D,
        foBadDecapsEvent encPKE decPKE (foReprogramKey G ω.1 ω.2.1) (Q_G ω.1) pk sk
          (ct_queries ω.1 i)
    let QueryChallenge : Ω → Prop := fun ω => ω.1 ∈ Q_G ω.1
    (dist.acceptWeight Real0 - dist.acceptWeight Real1).natAbs ≤
      2 * dist.eventMass BadDecaps + 2 * dist.eventMass QueryChallenge := by
  intro Ω dist Real0 Real1 BadDecaps QueryChallenge
  let Sim0 : Ω → Bool := fun ω =>
    let m_star := ω.1
    let k0 := ω.2.1
    let G' := foReprogramKey G m_star k0
    let ct_star := foEncDet encPKE G' pk m_star
    adv ct_star k0
      (fun i => foDecapsSim encPKE decPKE G' J (Q_G m_star) pk sk z (ct_queries m_star i))
  let Sim1 : Ω → Bool := fun ω =>
    let m_star := ω.1
    let k0 := ω.2.1
    let k1 := ω.2.2
    let G' := foReprogramKey G m_star k0
    let ct_star := foEncDet encPKE G' pk m_star
    adv ct_star k1
      (fun i => foDecapsSim encPKE decPKE G' J (Q_G m_star) pk sk z (ct_queries m_star i))
  let Ideal0 : Ω → Bool := fun ω =>
    let m_star := ω.1
    let k0 := ω.2.1
    let ct_star := foEncDet encPKE G pk m_star
    adv ct_star k0
      (fun i => foDecapsSim encPKE decPKE G J (Q_G m_star) pk sk z (ct_queries m_star i))
  let Ideal1 : Ω → Bool := fun ω =>
    let m_star := ω.1
    let k1 := ω.2.2
    let ct_star := foEncDet encPKE G pk m_star
    adv ct_star k1
      (fun i => foDecapsSim encPKE decPKE G J (Q_G m_star) pk sk z (ct_queries m_star i))
  apply fo_ind_cca2_security_reduction dist Real0 Real1 Sim0 Sim1 Ideal0 Ideal1
    BadDecaps QueryChallenge
  · intro ω h_nb
    dsimp [Real0, Sim0]
    have h_tr := foDecapsTranscript_eq_of_no_bad encPKE decPKE (foReprogramKey G ω.1 ω.2.1) J
      (Q_G ω.1) pk sk z (ct_queries ω.1) (fun i hi => h_nb ⟨i, hi⟩)
    rw [h_tr]
  · intro ω h_nb
    dsimp [Real1, Sim1]
    have h_tr := foDecapsTranscript_eq_of_no_bad encPKE decPKE (foReprogramKey G ω.1 ω.2.1) J
      (Q_G ω.1) pk sk z (ct_queries ω.1) (fun i hi => h_nb ⟨i, hi⟩)
    rw [h_tr]
  · intro ω h_nq
    dsimp [Sim0, Ideal0]
    rw [foEncDet_reprogramKey_eq]
    have h_sim_eq :
        (fun i => foDecapsSim encPKE decPKE (foReprogramKey G ω.1 ω.2.1) J (Q_G ω.1) pk sk z
          (ct_queries ω.1 i)) =
        (fun i => foDecapsSim encPKE decPKE G J (Q_G ω.1) pk sk z (ct_queries ω.1 i)) := by
      ext i
      exact foDecapsSim_reprogramKey_eq_of_not_mem encPKE decPKE G J (Q_G ω.1) ω.1 ω.2.1 pk sk z
        (ct_queries ω.1 i) h_nq
    rw [h_sim_eq]
  · intro ω h_nq
    dsimp [Sim1, Ideal1]
    rw [foEncDet_reprogramKey_eq]
    have h_sim_eq :
        (fun i => foDecapsSim encPKE decPKE (foReprogramKey G ω.1 ω.2.1) J (Q_G ω.1) pk sk z
          (ct_queries ω.1 i)) =
        (fun i => foDecapsSim encPKE decPKE G J (Q_G ω.1) pk sk z (ct_queries ω.1 i)) := by
      ext i
      exact foDecapsSim_reprogramKey_eq_of_not_mem encPKE decPKE G J (Q_G ω.1) ω.1 ω.2.1 pk sk z
        (ct_queries ω.1 i) h_nq
    rw [h_sim_eq]
  · dsimp [FinDist.acceptWeight, dist, uniformFinDist, Ideal0, Ideal1]
    let e : Ω ≃ Ω := Equiv.prodCongr (Equiv.refl Msg) (Equiv.prodComm Key Key)
    exact Equiv.sum_comp e (fun ω : Ω =>
      (1 : ℤ) * bitToInt (adv (foEncDet encPKE G pk ω.1) ω.2.2
        (fun i => foDecapsSim encPKE decPKE G J (Q_G ω.1) pk sk z (ct_queries ω.1 i))))

theorem modPKE_isCorrectFOPKE (params : LWEParams) (k N Δ t : ℕ) [Fact (0 < N)]
    {Coins Key : Type*}
    (G : ModPKEPublicKey (NegacyclicPoly (Zq params) N) k → (Fin N → ℕ) → Key × Coins)
    (expandR : Coins → VectorR (NegacyclicPoly (Zq params) N) k)
    (expandE1 : Coins → VectorR (NegacyclicPoly (Zq params) N) k)
    (expandE2 : Coins → NegacyclicPoly (Zq params) N)
    (A : MatrixR (NegacyclicPoly (Zq params) N) k k)
    (s e : VectorR (NegacyclicPoly (Zq params) N) k)
    (ht_le : Δ * t ≤ params.q)
    (hs_tern : ∀ i : Fin k, NegacyclicPoly.IsTernaryPoly (s i))
    (he_norm : ∀ i : Fin k, normInf params (e i).coeffs ≤ 1)
    (hr_tern : ∀ c : Coins, ∀ i : Fin k, NegacyclicPoly.IsTernaryPoly (expandR c i))
    (he1_norm : ∀ c : Coins, ∀ i : Fin k, normInf params (expandE1 c i).coeffs ≤ 1)
    (he2_norm : ∀ c : Coins, normInf params (expandE2 c).coeffs ≤ 1)
    (h_zero_fail : 2 * (2 * k * N + 1) < Δ) :
    let pk := modPKEKeygen (NegacyclicPoly (Zq params) N) k A s e
    let encPKE := fun pk' (m : { m : Fin N → ℕ // ∀ idx, m idx < t }) (c : Coins) =>
      modPKEEncrypt (NegacyclicPoly (Zq params) N) k pk' (expandR c) (expandE1 c) (expandE2 c)
        (bfvEncodePoly params N Δ m.1)
    let decPKE := fun s' (ct : ModPKECiphertext (NegacyclicPoly (Zq params) N) k) =>
      (bfvDecodePoly params N Δ (modPKEPhase (NegacyclicPoly (Zq params) N) k ct s'))
    ∀ m : { m : Fin N → ℕ // ∀ idx, m idx < t },
      decPKE s (foEncDet encPKE (fun pk' m' => G pk' m'.1) pk m) = m.1 := by
  intro pk encPKE decPKE m
  dsimp [foEncDet, encPKE, decPKE]
  set c := (G pk m.1).2
  have h_bound := modPKE_ternary_noise_bound params k N s e
    (expandR c) (expandE1 c) (expandE2 c)
    (hr_tern c) hs_tern he_norm (he1_norm c) (he2_norm c)
  have h_noise : 2 * normInf params
      (dotProductR (NegacyclicPoly (Zq params) N) k e (expandR c) + expandE2 c -
        dotProductR (NegacyclicPoly (Zq params) N) k s (expandE1 c)).coeffs < Δ := by omega
  exact modPKE_decrypt_correct params k N Δ t A s e (expandR c) (expandE1 c) (expandE2 c)
    m.1 ht_le m.2 h_noise

end FujisakiOkamotoINDCCA2Reduction

end LWE
