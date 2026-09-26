import TwoDoorsProof.DeterminantMatching
import TwoDoorsProof.Shortest

namespace TwoDoorsProof

open Matrix PowerSeries SimpleGraph
open scoped Matrix
noncomputable section

variable {V R : Type*} [DecidableEq V] [Fintype V] [CommRing R]

def markedCoeffSeries (p : (Marked R)⟦X⟧) : R⟦X⟧ :=
  PowerSeries.mk fun n => markedCoeff (PowerSeries.coeff n p)

theorem markedCoeffSeries_coeff (p : (Marked R)⟦X⟧) (n : ℕ) :
    PowerSeries.coeff n (markedCoeffSeries p) =
      markedCoeff (PowerSeries.coeff n p) := by
  simp [markedCoeffSeries]

theorem markedCoeffSeries_const_mul
    (p : R⟦X⟧) (q : (Marked R)⟦X⟧) :
    markedCoeffSeries (PowerSeries.map markConstHom p * q) =
      p * markedCoeffSeries q := by
  apply PowerSeries.ext
  intro n
  simp only [markedCoeffSeries_coeff, PowerSeries.coeff_mul]
  change (markedCoeffHom (R := R))
    (∑ ij ∈ Finset.antidiagonal n,
      PowerSeries.coeff ij.1 (PowerSeries.map markConstHom p) *
        PowerSeries.coeff ij.2 q) =
    ∑ ij ∈ Finset.antidiagonal n,
      PowerSeries.coeff ij.1 p *
        markedCoeff (PowerSeries.coeff ij.2 q)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro ij hij
  rw [PowerSeries.coeff_map]
  exact markedCoeff_markConst_mul _ _

theorem marked_geometric_coeffSeries
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s t : V) (a b : Sym2 V) (hab : a ≠ b)
    (z : Sym2 V → R) :
    markedCoeffSeries
        (matrixGeometric (weightedAdj G (markedEdgeWeight a b z)) s t) =
      seriesOf (walkSum' (G := G) (s := s) (t := t)
        (a := a) (b := b) z) := by
  apply PowerSeries.ext
  intro n
  simp only [markedCoeffSeries_coeff, seriesOf, PowerSeries.coeff_mk]
  rw [geometric_coeff (weightedAdj G (markedEdgeWeight a b z)) n s t]
  change markedCoeff ((weightedAdj G (markedEdgeWeight a b z) ^ n) s t) =
    walkSum G s t a b z n
  exact marked_matrix_pow_coefficient G s t a b hab z n

def ordinaryDenominator (G : SimpleGraph V) [DecidableRel G.Adj]
    (a b : Sym2 V) (z : Sym2 V → R) : R⟦X⟧ :=
  (matrixResolvent (weightedAdj G (ordinaryEdgeWeight a b z))).det

def determinantNumerator (G : SimpleGraph V) [DecidableRel G.Adj]
    (s t : V) (a b : Sym2 V) (z : Sym2 V → R) : R⟦X⟧ :=
  markedCoeffSeries
    ((matrixResolvent (weightedAdj G (markedEdgeWeight a b z))).adjugate s t)

theorem ordinaryDenominator_constant_one
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (a b : Sym2 V) (z : Sym2 V → R) :
    PowerSeries.coeff 0 (ordinaryDenominator G a b z) = 1 :=
  resolvent_det_constant_one _

theorem determinant_generating_identity [CharP R 2]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s t : V) (a b : Sym2 V) (hab : a ≠ b)
    (z : Sym2 V → R) :
    seriesOf (walkSum' (G := G) (s := s) (t := t)
      (a := a) (b := b) z) * ordinaryDenominator G a b z =
        determinantNumerator G s t a b z := by
  have h := det_mul_geometric_eq_adjugate
    (weightedAdj G (markedEdgeWeight a b z)) s t
  rw [marked_denominator_eq_ordinary G a b hab z,
    ordinary_denominator_eq_map G a b z] at h
  have hcoeff := congrArg (markedCoeffSeries (R := R)) h
  rw [markedCoeffSeries_const_mul,
    marked_geometric_coeffSeries G s t a b hab z] at hcoeff
  simpa only [ordinaryDenominator, determinantNumerator, mul_comm] using hcoeff

end
end TwoDoorsProof
