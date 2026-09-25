import TwoDoorsProof.WalkSum
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# The first nonzero layer

This file isolates the common conclusion of both proofs in the editorial.
The graph-theoretic work supplies a shortest target path. The involution proof
supplies cancellation of the non-path walks. The determinant proof supplies the
same cancellation through a formal power-series quotient.
-/

namespace TwoDoorsProof

open SimpleGraph

variable {V R : Type*} [DecidableEq V] [Fintype V]
  {G : SimpleGraph V} [DecidableRel G.Adj] {s t : V} {a b : Sym2 V}

def IsTargetWalk (p : G.Walk s t) : Prop :=
  p.edges.count a = 1 ∧ p.edges.count b = 1

def IsTargetPath (p : G.Walk s t) : Prop :=
  p.IsPath ∧ IsTargetWalk (G := G) (s := s) (t := t) (a := a) (b := b) p

def IsShortestTargetPath (d : ℕ) : Prop :=
  ∃ p : G.Walk s t, IsTargetPath (a := a) (b := b) p ∧ p.length = d ∧
    ∀ q : G.Walk s t, IsTargetPath (a := a) (b := b) q → d ≤ q.length

def pathSum' [CommRing R] (z : Sym2 V → R) (d : ℕ) : R :=
  ∑ p ∈ targetPaths G s t a b d, walkWeight G s t z p

def walkSum' [CommRing R] (z : Sym2 V → R) (d : ℕ) : R :=
  ∑ p ∈ targetWalks G s t a b d, walkWeight G s t z p

structure InvolutionCertificate [CommRing R] (z : Sym2 V → R) (d : ℕ) where
  pair : ∀ p ∈ targetNonpaths G s t a b d, G.Walk s t
  mem : ∀ p hp, pair p hp ∈ targetNonpaths G s t a b d
  fixedFree : ∀ p hp, pair p hp ≠ p
  involutive : ∀ p hp, pair (pair p hp) (mem p hp) = p
  weight_preserved : ∀ p hp,
    walkWeight G s t z (pair p hp) = walkWeight G s t z p

theorem walkSum_eq_pathSum_of_certificate [CommRing R]
    (h₂ : ∀ x : R, x + x = 0) (z : Sym2 V → R) (d : ℕ)
    (h : InvolutionCertificate (G := G) (s := s) (t := t) (a := a) (b := b) z d) :
    walkSum' (G := G) (s := s) (t := t) (a := a) (b := b) z d =
      pathSum' (G := G) (s := s) (t := t) (a := a) (b := b) z d := by
  exact walkSum_eq_pathSum_of_involution G s t a b h₂ z d h.pair h.mem
    h.fixedFree h.involutive h.weight_preserved

theorem pathSum'_eq_zero_of_no_target_path [CommRing R] (z : Sym2 V → R)
    (d : ℕ) (h : ¬ ∃ p : G.Walk s t,
      IsTargetPath (a := a) (b := b) p ∧ p.length = d) :
    pathSum' (G := G) (s := s) (t := t) (a := a) (b := b) z d = 0 := by
  unfold pathSum' targetPaths
  apply Finset.sum_eq_zero
  intro p hp
  exfalso
  apply h
  refine ⟨p, ?_, ?_⟩
  · have htw := (Finset.mem_filter.mp hp).1
    exact ⟨(Finset.mem_filter.mp hp).2, (Finset.mem_filter.mp htw).2⟩
  · have ht := (Finset.mem_filter.mp hp).1
    have hmem : p ∈ (G.finsetWalkLength d s t : Set (G.Walk s t)) :=
      Finset.mem_coe.mpr (Finset.mem_filter.mp ht).1
    rw [SimpleGraph.coe_finsetWalkLength_eq] at hmem
    exact hmem

structure PalindromeReversalCertificate [CommRing R] (z : Sym2 V → R)
    (dStar : ℕ) where
  layer : ∀ d, d ≤ dStar → InvolutionCertificate (G := G) (s := s) (t := t)
    (a := a) (b := b) z d

theorem first_nonzero_of_palindrome_reversal
    [CommRing R] (h₂ : ∀ x : R, x + x = 0) (z : Sym2 V → R)
    (dStar : ℕ) (hshort : ∀ d, d < dStar →
      ¬ ∃ p : G.Walk s t,
        IsTargetPath (a := a) (b := b) p ∧ p.length = d)
    (hstar_ne : pathSum' (G := G) (s := s) (t := t) (a := a) (b := b) z dStar ≠ 0)
    (hrev : PalindromeReversalCertificate (G := G) (s := s) (t := t)
      (a := a) (b := b) z dStar) :
    (∀ d, d < dStar → walkSum' (G := G) (s := s) (t := t) (a := a) (b := b) z d = 0) ∧
    walkSum' (G := G) (s := s) (t := t) (a := a) (b := b) z dStar ≠ 0 := by
  constructor
  · intro d hd
    rw [walkSum_eq_pathSum_of_certificate h₂ z d (hrev.layer d (Nat.le_of_lt hd))]
    exact pathSum'_eq_zero_of_no_target_path z d (hshort d hd)
  · rw [walkSum_eq_pathSum_of_certificate h₂ z dStar (hrev.layer dStar le_rfl)]
    exact hstar_ne

section PowerSeries

open PowerSeries

theorem coeff_eq_of_mul_eq_of_previous_zero [CommRing R]
    (f g h : R⟦X⟧) (n : ℕ) (hprod : f * g = h)
    (hg0 : coeff 0 g = 1) (hfzero : ∀ k, k < n → coeff k f = 0) :
    coeff n f = coeff n h := by
  have hc := congrArg (coeff n) hprod
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ] at hc
  have hsum :
      ∑ k ∈ Finset.range n, coeff k f * coeff (n - k) g = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [hfzero k (Finset.mem_range.mp hk), zero_mul]
  rw [hsum] at hc
  simpa [hg0] using hc

def seriesOf (f : ℕ → R) : R⟦X⟧ :=
  PowerSeries.mk f

structure DeterminantExpansionCertificate [CommRing R] (z : Sym2 V → R)
    (dStar : ℕ) where
  numerator : R⟦X⟧
  denominator : R⟦X⟧
  denominator_constant : coeff 0 denominator = 1
  generating_identity :
    seriesOf (walkSum' (G := G) (s := s) (t := t) (a := a) (b := b) z) *
      denominator = numerator
  numerator_coeff :
    ∀ d, coeff d numerator =
      pathSum' (G := G) (s := s) (t := t) (a := a) (b := b) z d

theorem first_nonzero_of_determinant_expansion
    [CommRing R] (z : Sym2 V → R) (dStar : ℕ)
    (hshort : ∀ d, d < dStar →
      ¬ ∃ p : G.Walk s t,
        IsTargetPath (a := a) (b := b) p ∧ p.length = d)
    (hstar_ne : pathSum' (G := G) (s := s) (t := t) (a := a) (b := b) z dStar ≠ 0)
    (hdet : DeterminantExpansionCertificate (G := G) (s := s) (t := t)
      (a := a) (b := b) z dStar) :
    (∀ d, d < dStar → walkSum' (G := G) (s := s) (t := t) (a := a) (b := b) z d = 0) ∧
    walkSum' (G := G) (s := s) (t := t) (a := a) (b := b) z dStar ≠ 0 := by
  have hzero : ∀ d, d < dStar →
      walkSum' (G := G) (s := s) (t := t) (a := a) (b := b) z d = 0 := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro hd
      have hp : pathSum' (G := G) (s := s) (t := t) (a := a) (b := b) z d = 0 :=
        pathSum'_eq_zero_of_no_target_path z d (hshort d hd)
      have hprev : ∀ k, k < d →
          coeff k (seriesOf (walkSum' (G := G) (s := s) (t := t)
            (a := a) (b := b) z)) = 0 := by
        intro k hk
        simpa [seriesOf, coeff_mk] using ih k hk (Nat.lt_trans hk hd)
      have heq := coeff_eq_of_mul_eq_of_previous_zero
        (seriesOf (walkSum' (G := G) (s := s) (t := t) (a := a) (b := b) z))
        hdet.denominator hdet.numerator d hdet.generating_identity
        hdet.denominator_constant hprev
      have hn : coeff d hdet.numerator = 0 := by
        rw [hdet.numerator_coeff d, hp]
      have : coeff d (seriesOf (walkSum' (G := G) (s := s) (t := t)
          (a := a) (b := b) z)) = 0 := heq.trans hn
      simpa [seriesOf, coeff_mk] using this
  constructor
  · exact hzero
  · have heq := coeff_eq_of_mul_eq_of_previous_zero
      (seriesOf (walkSum' (G := G) (s := s) (t := t) (a := a) (b := b) z))
      hdet.denominator hdet.numerator dStar hdet.generating_identity
      hdet.denominator_constant (fun k hk => by
        simpa [seriesOf, coeff_mk] using hzero k hk)
    rw [hdet.numerator_coeff dStar] at heq
    have heq' :
        walkSum' (G := G) (s := s) (t := t) (a := a) (b := b) z dStar =
          pathSum' (G := G) (s := s) (t := t) (a := a) (b := b) z dStar := by
      simpa [seriesOf, coeff_mk] using heq
    intro hzeroStar
    apply hstar_ne
    rw [← heq']
    exact hzeroStar

end PowerSeries

end TwoDoorsProof
