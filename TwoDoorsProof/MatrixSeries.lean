import TwoDoorsProof.MatrixWalk
import Mathlib.RingTheory.PowerSeries.Basic

namespace TwoDoorsProof

open Matrix PowerSeries
open scoped Matrix
noncomputable section

variable {V R : Type*} [DecidableEq V] [Fintype V] [CommRing R]

def seriesMatrix (M : Matrix V V R) : Matrix V V R⟦X⟧ :=
  M.map PowerSeries.C

def matrixGeometric (M : Matrix V V R) : Matrix V V R⟦X⟧ :=
  fun i j => PowerSeries.mk fun n => (M ^ n) i j

def matrixResolvent (M : Matrix V V R) : Matrix V V R⟦X⟧ :=
  1 - (PowerSeries.X : R⟦X⟧) • seriesMatrix M

theorem geometric_coeff (M : Matrix V V R) (n : ℕ) (i j : V) :
    PowerSeries.coeff n (matrixGeometric M i j) = (M ^ n) i j := by
  simp [matrixGeometric]

theorem seriesMatrix_mul_geometric_coeff (M : Matrix V V R)
    (n : ℕ) (i j : V) :
    PowerSeries.coeff n ((seriesMatrix M * matrixGeometric M) i j) =
      (M ^ (n + 1)) i j := by
  simp only [Matrix.mul_apply, map_sum, seriesMatrix, Matrix.map_apply,
    PowerSeries.coeff_C_mul, geometric_coeff]
  rw [pow_succ']
  rfl

theorem geometric_recurrence (M : Matrix V V R) :
    matrixGeometric M =
      1 + (PowerSeries.X : R⟦X⟧) •
        (seriesMatrix M * matrixGeometric M) := by
  ext i j n
  cases n with
  | zero =>
      simp [geometric_coeff, Matrix.one_apply, matrixGeometric]
  | succ n =>
      simp [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
        geometric_coeff, seriesMatrix_mul_geometric_coeff]
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

theorem resolvent_mul_geometric (M : Matrix V V R) :
    matrixResolvent M * matrixGeometric M = 1 := by
  rw [matrixResolvent, sub_mul, Matrix.one_mul]
  rw [Matrix.smul_mul]
  have h := geometric_recurrence M
  nth_rewrite 1 [h]
  abel

theorem det_mul_geometric_eq_adjugate (M : Matrix V V R)
    (i j : V) :
    (matrixResolvent M).det * matrixGeometric M i j =
      (matrixResolvent M).adjugate i j := by
  have h := Matrix.adjugate_mul (matrixResolvent M)
  have h' : (matrixResolvent M).adjugate *
      (matrixResolvent M * matrixGeometric M) =
      (matrixResolvent M).det • matrixGeometric M := by
    rw [← Matrix.mul_assoc, h, Matrix.smul_mul, Matrix.one_mul]
  rw [resolvent_mul_geometric] at h'
  simpa [Matrix.smul_apply, smul_eq_mul] using congrArg (fun A : Matrix V V R⟦X⟧ => A i j) h'.symm

end
end TwoDoorsProof
