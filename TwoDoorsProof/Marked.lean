import TwoDoorsProof.Determinant
import TwoDoorsProof.WalkSum
import Mathlib.Algebra.DualNumber

namespace TwoDoorsProof

/-- Two independent square-zero markers, represented by nested dual numbers. -/
abbrev Marked (R : Type*) := DualNumber (DualNumber R)

def alpha {R : Type*} [Semiring R] : Marked R :=
  TrivSqZeroExt.inl DualNumber.eps

def beta {R : Type*} [Semiring R] : Marked R :=
  DualNumber.eps

def markedCoeff {R : Type*} [Semiring R] (x : Marked R) : R :=
  TrivSqZeroExt.snd (TrivSqZeroExt.snd x)

def markConst {R : Type*} [Semiring R] (x : R) : Marked R :=
  TrivSqZeroExt.inl (TrivSqZeroExt.inl x)

def constantCoeff {R : Type*} [Semiring R] (x : Marked R) : R :=
  TrivSqZeroExt.fst (TrivSqZeroExt.fst x)

def firstCoeff {R : Type*} [Semiring R] (x : Marked R) : R :=
  TrivSqZeroExt.snd (TrivSqZeroExt.fst x)

def secondCoeff {R : Type*} [Semiring R] (x : Marked R) : R :=
  TrivSqZeroExt.fst (TrivSqZeroExt.snd x)

theorem markedCoeff_add {R : Type*} [Semiring R] (x y : Marked R) :
    markedCoeff (x + y) = markedCoeff x + markedCoeff y := rfl

def markedCoeffHom {R : Type*} [Semiring R] : Marked R →+ R where
  toFun := markedCoeff
  map_zero' := rfl
  map_add' := markedCoeff_add

theorem markedCoeff_mul {R : Type*} [CommSemiring R] (x y : Marked R) :
    markedCoeff (x * y) =
      constantCoeff x * markedCoeff y +
      firstCoeff x * secondCoeff y +
      secondCoeff x * firstCoeff y +
      markedCoeff x * constantCoeff y := by
  simp only [markedCoeff, constantCoeff, firstCoeff, secondCoeff,
    DualNumber.snd_mul, TrivSqZeroExt.snd_add]
  ring

theorem markedCoeff_markConst {R : Type*} [Semiring R] (x : R) :
    markedCoeff (markConst x) = 0 := rfl

theorem markedCoeff_markConst_mul {R : Type*} [CommSemiring R]
    (x : R) (y : Marked R) :
    markedCoeff (markConst x * y) = x * markedCoeff y := by
  simp [markedCoeff, markConst]

theorem markConst_one {R : Type*} [Semiring R] :
    markConst (1 : R) = 1 := by
  simp [markConst]

theorem markConst_mul {R : Type*} [CommSemiring R] (x y : R) :
    markConst (x * y) = markConst x * markConst y := by
  simp [markConst]

def markConstHom {R : Type*} [CommSemiring R] : R →+* Marked R where
  toFun := markConst
  map_zero' := rfl
  map_one' := markConst_one
  map_add' := by intros; simp [markConst]
  map_mul' := markConst_mul

def markedEdgeWeight {E R : Type*} [DecidableEq E] [CommSemiring R]
    (a b : E) (z : E → R) (e : E) : Marked R :=
  alpha ^ (if e = a then 1 else 0) *
    beta ^ (if e = b then 1 else 0) * markConst (z e)

theorem marked_product_count {E R : Type*} [DecidableEq E] [CommSemiring R]
    (a b : E) (hab : a ≠ b) (z : E → R) (l : List E) :
    (l.map (markedEdgeWeight a b z)).prod =
      (alpha : Marked R) ^ l.count a *
        beta ^ l.count b * markConst ((l.map z).prod) := by
  induction l with
  | nil => simp [markConst_one]
  | cons e es ih =>
      by_cases ha : e = a
      · subst e
        simp [markedEdgeWeight, hab, ih, pow_succ, markConst_mul]
        ring
      · by_cases hb : e = b
        · subst e
          simp [markedEdgeWeight, ha, ih, pow_succ, markConst_mul]
          ring
        · simp [markedEdgeWeight, ha, hb, ih, markConst_mul]
          ring

theorem alpha_sq {R : Type*} [CommSemiring R] :
    (alpha : Marked R) ^ 2 = 0 := by
  simp [alpha, pow_two, TrivSqZeroExt.inl_mul_inl]

theorem beta_sq {R : Type*} [CommSemiring R] :
    (beta : Marked R) ^ 2 = 0 := DualNumber.eps_pow_two

theorem markedEdgeWeight_eq_const {E R : Type*} [DecidableEq E] [CommSemiring R]
    (a b e : E) (z : E → R) (ha : e ≠ a) (hb : e ≠ b) :
    markedEdgeWeight a b z e = markConst (z e) := by
  simp [markedEdgeWeight, ha, hb]

theorem markedEdgeWeight_sq_special {E R : Type*}
    [DecidableEq E] [CommSemiring R]
    (a b : E) (hab : a ≠ b) (z : E → R) (e : E)
    (he : e = a ∨ e = b) :
    (markedEdgeWeight a b z e) ^ 2 = 0 := by
  rcases he with rfl | rfl
  · have h : markedEdgeWeight e b z e =
        (alpha : Marked R) * markConst (z e) := by
      simp [markedEdgeWeight, hab]
    rw [h]
    calc
      ((alpha : Marked R) * markConst (z e)) ^ 2 =
          alpha ^ 2 * markConst (z e) ^ 2 := by ring
      _ = 0 := by rw [alpha_sq]; simp
  · have h : markedEdgeWeight a e z e =
        (beta : Marked R) * markConst (z e) := by
      simp [markedEdgeWeight, Ne.symm hab]
    rw [h]
    calc
      ((beta : Marked R) * markConst (z e)) ^ 2 =
          beta ^ 2 * markConst (z e) ^ 2 := by ring
      _ = 0 := by rw [beta_sq]; simp

theorem markedCoeff_one {R : Type*} [Semiring R] :
    markedCoeff (1 : Marked R) = 0 := rfl

theorem markedCoeff_alpha {R : Type*} [Semiring R] :
    markedCoeff (alpha : Marked R) = 0 := rfl

theorem markedCoeff_beta {R : Type*} [Semiring R] :
    markedCoeff (beta : Marked R) = 0 := rfl

theorem markedCoeff_alpha_beta {R : Type*} [CommSemiring R] :
    markedCoeff ((alpha : Marked R) * beta) = 1 := by
  simp [markedCoeff, alpha, beta]

theorem markedCoeff_powers {R : Type*} [CommSemiring R]
    (n m : ℕ) (x : R) :
    markedCoeff ((alpha : Marked R) ^ n * beta ^ m * markConst x) =
      if n = 1 ∧ m = 1 then x else 0 := by
  have halpha (k : ℕ) : (alpha : Marked R) ^ (2 + k) = 0 := by
    rw [pow_add, alpha_sq, zero_mul]
  have hbeta (k : ℕ) : (beta : Marked R) ^ (2 + k) = 0 := by
    rw [pow_add, beta_sq, zero_mul]
  rcases n with _ | _ | n
  · rcases m with _ | _ | m
    · simp [markedCoeff_markConst]
    · simp [markedCoeff, beta, markConst]
    · simp [show m + 2 = 2 + m by omega, hbeta, markedCoeff]
  · rcases m with _ | _ | m
    · simp [markedCoeff, alpha, markConst]
    · simp only [Nat.zero_add, pow_one, true_and, ite_true]
      rw [mul_comm ((alpha : Marked R) * beta) (markConst x),
        markedCoeff_markConst_mul, markedCoeff_alpha_beta, mul_one]
    · simp [show m + 2 = 2 + m by omega, hbeta, markedCoeff,
        show (2 + m : ℕ) ≠ 1 by omega]
  · simp [show n + 2 = 2 + n by omega, halpha, markedCoeff,
      show (2 + n : ℕ) ≠ 1 by omega]

theorem marked_product_coefficient {E R : Type*}
    [DecidableEq E] [CommSemiring R] (a b : E) (hab : a ≠ b)
    (z : E → R) (l : List E) :
    markedCoeff ((l.map (markedEdgeWeight a b z)).prod) =
      if l.count a = 1 ∧ l.count b = 1 then (l.map z).prod else 0 := by
  rw [marked_product_count a b hab z l, markedCoeff_powers]

theorem marked_walk_sum_coefficient
    {V R : Type*} [DecidableEq V] [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    [CommRing R] (u v : V) (a b : Sym2 V) (hab : a ≠ b)
    (z : Sym2 V → R) (d : ℕ) :
    markedCoeff
        (∑ w ∈ G.finsetWalkLength d u v,
          walkWeight G u v (markedEdgeWeight a b z) w) =
      walkSum G u v a b z d := by
  change (markedCoeffHom (R := R))
      (∑ w ∈ G.finsetWalkLength d u v,
        walkWeight G u v (markedEdgeWeight a b z) w) = _
  rw [map_sum]
  change (∑ w ∈ G.finsetWalkLength d u v,
    markedCoeff (walkWeight G u v (markedEdgeWeight a b z) w)) = _
  unfold walkSum targetWalks
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro w hw
  simp only [walkWeight]
  exact marked_product_coefficient a b hab z w.edges

end TwoDoorsProof
