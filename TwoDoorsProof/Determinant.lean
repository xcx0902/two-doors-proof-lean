import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.RowCol

/-!
# The marked directed edge in the determinant argument

Adding a *directed* formal edge in position `(t,s)` is a rank-one change, even
if the original symmetric adjacency matrix already has a nonzero `(t,s)`
entry. The coefficient of its independent weight is the cofactor `(t,s)`,
which is the `(s,t)` entry of the adjugate.
-/

namespace TwoDoorsProof

open Matrix

variable {V R : Type*} [Fintype V] [DecidableEq V] [CommRing R]

theorem det_add_directed_edge (Q : Matrix V V R) (s t : V) (y : R) :
    (Q + Matrix.single t s y).det = Q.det + y * Q.adjugate s t := by
  have hrow : Q + Matrix.single t s y =
      Q.updateRow t (Q t + Pi.single s y) := by
    ext i j
    by_cases hi : i = t
    · subst i
      simp [Matrix.single_apply, Matrix.updateRow_apply, Pi.single_apply, eq_comm]
    · have ht : t ≠ i := Ne.symm hi
      simp [Matrix.updateRow_apply, hi, ht]
  rw [hrow, Matrix.det_updateRow_add, Matrix.updateRow_eq_self]
  have hs : (Pi.single s y : V → R) = y • Pi.single s 1 := by
    ext i
    simp [Pi.single_apply, smul_eq_mul, mul_ite]
  rw [hs, Matrix.det_updateRow_smul, Matrix.adjugate_apply]

/-- The adjugate identity used before expanding the determinant into cycles.
No nonsingularity is assumed: this is an identity over any commutative ring. -/
theorem resolvent_cofactor (Q : Matrix V V R) (s t : V) :
    Q.det * Q.adjugate s t =
      (Q + Matrix.single t s 1).det * Q.det - Q.det ^ 2 := by
  rw [det_add_directed_edge]
  ring

end TwoDoorsProof
