import TwoDoorsProof.DeterminantPathExpansion
import TwoDoorsProof.Weights

namespace TwoDoorsProof

open SimpleGraph PowerSeries
noncomputable section

variable {V : Type*} [DecidableEq V] [Fintype V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {s t : V} {a b : Sym2 V}

private theorem polynomial_add_self_zero'
    (x : MvPolynomial (Sym2 V) (ZMod 2)) : x + x = 0 := by
  ext m
  simp [CharTwo.add_self_eq_zero]

def concreteDeterminantExpansionCertificate
    (dStar : ℕ)
    (hst : s ≠ t) (hab : a ≠ b)
    (hmin : ∀ q : G.Walk s t, IsTargetPath (a := a) (b := b) q →
      dStar ≤ q.length) :
    DeterminantExpansionCertificate
      (G := G) (s := s) (t := t) (a := a) (b := b)
      (MvPolynomial.X : Sym2 V → MvPolynomial (Sym2 V) (ZMod 2)) dStar := by
  let z : Sym2 V → MvPolynomial (Sym2 V) (ZMod 2) := MvPolynomial.X
  refine
    { numerator := determinantNumerator G s t a b z
      denominator := ordinaryDenominator G a b z
      denominator_constant := ordinaryDenominator_constant_one G a b z
      generating_identity := determinant_generating_identity
        (h₂ := polynomial_add_self_zero' (V := V))
        (G := G) (s := s) (t := t) (a := a) (b := b)
        (hab := hab) (z := z)
      numerator_coeff := by
        intro d hd
        exact determinantNumerator_coeff_eq_pathSum_of_minimal
          (polynomial_add_self_zero' (V := V))
          G s t hst a b hab z dStar d hd hmin
    }

theorem first_nonzero_of_concrete_determinant
    (dStar : ℕ) (hab : a ≠ b)
    (hshort : IsShortestTargetPath (G := G) (s := s) (t := t)
      (a := a) (b := b) dStar) :
    (∀ d, d < dStar →
      walkSum' (G := G) (s := s) (t := t) (a := a) (b := b)
        (MvPolynomial.X : Sym2 V → MvPolynomial (Sym2 V) (ZMod 2)) d = 0) ∧
      walkSum' (G := G) (s := s) (t := t) (a := a) (b := b)
        (MvPolynomial.X : Sym2 V → MvPolynomial (Sym2 V) (ZMod 2)) dStar ≠ 0 := by
  obtain ⟨p, hpath, hlen, hmin⟩ := hshort
  have hst : s ≠ t := by
    intro heq
    have hnil : p.Nil := hpath.1.nil_iff_eq.mpr heq
    have hzero : p.length = 0 := hnil.length_eq_zero
    have hcount : p.edges.count a ≤ p.edges.length :=
      List.count_le_length
    rw [hpath.2.1, p.length_edges, hzero] at hcount
    omega
  have hshort' :
      IsShortestTargetPath (G := G) (s := s) (t := t)
        (a := a) (b := b) dStar :=
    ⟨p, hpath, hlen, hmin⟩
  have hprevious : ∀ d, d < dStar →
      ¬ ∃ q : G.Walk s t,
        IsTargetPath (a := a) (b := b) q ∧ q.length = d := by
    intro d hd ⟨q, hq, hqden⟩
    have hqmin := hmin q hq
    omega
  exact first_nonzero_of_determinant_expansion
    (MvPolynomial.X : Sym2 V → MvPolynomial (Sym2 V) (ZMod 2))
    dStar hprevious
    (pathSum_X_ne_zero_of_shortest hshort')
    (concreteDeterminantExpansionCertificate dStar hst hab hmin)

theorem walkSum_X_eq_zero_of_no_target_path_determinant
    (hst : s ≠ t) (hab : a ≠ b)
    (hno : ¬ ∃ p : G.Walk s t,
      IsTargetPath (a := a) (b := b) p)
    (d : ℕ) :
    walkSum' (G := G) (s := s) (t := t) (a := a) (b := b)
      (MvPolynomial.X : Sym2 V → MvPolynomial (Sym2 V) (ZMod 2)) d = 0 := by
  let z : Sym2 V → MvPolynomial (Sym2 V) (ZMod 2) := MvPolynomial.X
  have hmin : ∀ q : G.Walk s t,
      IsTargetPath (a := a) (b := b) q → d ≤ q.length :=
    fun q hq => False.elim (hno ⟨q, hq⟩)
  let hdet := concreteDeterminantExpansionCertificate
    (G := G) (s := s) (t := t) (a := a) (b := b) d hst hab hmin
  have hnzero : ∀ k, k ≤ d → PowerSeries.coeff k hdet.numerator = 0 := by
    intro k hk
    rw [hdet.numerator_coeff k hk]
    apply pathSum'_eq_zero_of_no_target_path z k
    intro ⟨q, hq, _⟩
    exact hno ⟨q, hq⟩
  have hwzero : ∀ k, k ≤ d →
      walkSum' (G := G) (s := s) (t := t)
        (a := a) (b := b) z k = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro hk
      have hprev : ∀ j, j < k →
          PowerSeries.coeff j
            (seriesOf (walkSum' (G := G) (s := s) (t := t)
              (a := a) (b := b) z)) = 0 := by
        intro j hj
        simpa [seriesOf] using ih j hj (by omega)
      have hcoeff := coeff_eq_of_mul_eq_of_previous_zero
        (seriesOf (walkSum' (G := G) (s := s) (t := t)
          (a := a) (b := b) z))
        hdet.denominator hdet.numerator k hdet.generating_identity
        hdet.denominator_constant hprev
      simpa [seriesOf] using hcoeff.trans (hnzero k hk)
  exact hwzero d le_rfl

end
end TwoDoorsProof
