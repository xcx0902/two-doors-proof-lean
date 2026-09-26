import TwoDoorsProof.ComplementDenominator
import TwoDoorsProof.DeterminantGenerating

namespace TwoDoorsProof

open Matrix PowerSeries SimpleGraph
open scoped Matrix

noncomputable section

variable {V R : Type*} [DecidableEq V] [Fintype V] [CommRing R]
variable {s t : V}

def pathComplementDenominator (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : DirectedPathList s t) (a b : Sym2 V)
    (z : Sym2 V → R) : R⟦X⟧ :=
  ((matrixResolvent (weightedAdj G (ordinaryEdgeWeight a b z))).submatrix
    (fun x : {x : V // x ∉ p.list} => (x : V))
    (fun x : {x : V // x ∉ p.list} => (x : V))).det

theorem pathComplementDenominator_constant_one
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : DirectedPathList s t) (a b : Sym2 V)
    (z : Sym2 V → R) :
    coeff 0 (pathComplementDenominator G p a b z) = 1 := by
  unfold pathComplementDenominator
  exact matrixResolvent_submatrix_det_constant_one _
    (fun x : {x : V // x ∉ p.list} => (x : V))
    Subtype.coe_injective

theorem marked_cofactor_path_expansion
    (h₂ : ∀ x : R, x + x = 0)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s t : V) (hst : s ≠ t)
    (a b : Sym2 V) (hab : a ≠ b) (z : Sym2 V → R) :
    (matrixResolvent (weightedAdj G (markedEdgeWeight a b z))).adjugate s t =
      ∑ p : DirectedPathList s t,
        (X ^ (p.list.length - 1) *
          C (pathMatrixWeight (weightedAdj G (markedEdgeWeight a b z)) p)) *
          PowerSeries.map markConstHom
            (pathComplementDenominator G p a b z) := by
  let M := weightedAdj G (markedEdgeWeight a b z)
  have h₂marked : ∀ x : Marked R, x + x = 0 := by
    intro x
    ext <;> simp [h₂]
  have h₂series : ∀ x : (Marked R)⟦X⟧, x + x = 0 := by
    intro x
    apply PowerSeries.ext
    intro n
    simpa only [map_add, map_zero] using h₂marked (PowerSeries.coeff n x)
  rw [cofactor_path_complement_expansion h₂series
    (matrixResolvent M) hst]
  apply Fintype.sum_congr
  intro p
  rw [pathCycleWeight_resolvent h₂marked M p]
  congr 1
  exact complement_marked_det_is_const h₂ G p a b hab z

end
end TwoDoorsProof
