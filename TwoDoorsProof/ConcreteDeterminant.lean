import TwoDoorsProof.DeterminantGenerating
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
    (hab : a ≠ b)
    (hmin : ∀ q : G.Walk s t, IsTargetPath (a := a) (b := b) q →
      dStar ≤ q.length) :
    DeterminantExpansionCertificate
      (G := G) (s := s) (t := t) (a := a) (b := b)
      (MvPolynomial.X : Sym2 V → MvPolynomial (Sym2 V) (ZMod 2)) dStar := by
  let z : Sym2 V → MvPolynomial (Sym2 V) (ZMod 2) := MvPolynomial.X
  let hrev :=
    palindrome_reversal_certificate_of_minimal
      (G := G) (s := s) (t := t) (a := a) (b := b)
      z dStar hmin
  have hwalkpath : ∀ d, d ≤ dStar →
      walkSum' (G := G) (s := s) (t := t) (a := a) (b := b) z d =
        pathSum' (G := G) (s := s) (t := t) (a := a) (b := b) z d := by
    intro d hd
    exact walkSum_eq_pathSum_of_certificate
      (polynomial_add_self_zero' (V := V)) z d (hrev.layer d hd)
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
        have hprev : ∀ k, k < d →
            PowerSeries.coeff k
                (seriesOf (walkSum' (G := G) (s := s) (t := t)
                  (a := a) (b := b) z)) = 0 := by
          intro k hk
          have hpath : pathSum' (G := G) (s := s) (t := t)
              (a := a) (b := b) z k = 0 := by
            apply pathSum'_eq_zero_of_no_target_path z k
            intro ⟨q, hq, hlen⟩
            have := hmin q hq
            omega
          have hw :
              walkSum' (G := G) (s := s) (t := t) (a := a) (b := b) z k = 0 :=
            (hwalkpath k (by omega)).trans hpath
          simpa [seriesOf, hw]
        have heq := coeff_eq_of_mul_eq_of_previous_zero
          (seriesOf (walkSum' (G := G) (s := s) (t := t)
            (a := a) (b := b) z))
          (ordinaryDenominator G a b z)
          (determinantNumerator G s t a b z) d
          (determinant_generating_identity
            (h₂ := polynomial_add_self_zero' (V := V))
            (G := G) (s := s) (t := t) (a := a) (b := b)
            (hab := hab) (z := z))
          (ordinaryDenominator_constant_one G a b z) hprev
        have heq' :
            walkSum' (G := G) (s := s) (t := t) (a := a) (b := b) z d =
              PowerSeries.coeff d (determinantNumerator G s t a b z) := by
          simpa [seriesOf] using heq
        exact heq'.symm.trans (hwalkpath d hd)
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
    (concreteDeterminantExpansionCertificate dStar hab hmin)

end
end TwoDoorsProof
