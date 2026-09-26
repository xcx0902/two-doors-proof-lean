import TwoDoorsProof.CofactorPaths
import TwoDoorsProof.DeterminantMatching

namespace TwoDoorsProof

open Matrix PowerSeries

noncomputable section

variable {V R : Type*} [DecidableEq V] [Fintype V] [CommRing R]
variable {s t : V}

theorem matrixResolvent_submatrix
    {W : Type*} [DecidableEq W] [Fintype W]
    (M : Matrix V V R) (e : W → V) (he : Function.Injective e) :
    (matrixResolvent M).submatrix e e =
      matrixResolvent (M.submatrix e e) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [matrixResolvent, seriesMatrix, Matrix.one_apply]
  · have heq : e i ≠ e j := fun h => hij (he h)
    simp [matrixResolvent, seriesMatrix, Matrix.one_apply, hij, heq]

theorem matrixResolvent_submatrix_det_constant_one
    {W : Type*} [DecidableEq W] [Fintype W]
    (M : Matrix V V R) (e : W → V) (he : Function.Injective e) :
    PowerSeries.coeff 0
        ((matrixResolvent M).submatrix e e).det = 1 := by
  rw [matrixResolvent_submatrix M e he]
  exact resolvent_det_constant_one _

def pathMatrixWeight (M : Matrix V V R) (p : DirectedPathList s t) : R :=
  ∏ x ∈ p.list.toFinset.erase t, M x (cycleOfPath p x)

theorem pathCycleWeight_resolvent
    (h₂ : ∀ x : R, x + x = 0)
    (M : Matrix V V R) (p : DirectedPathList s t) :
    cycleMonomial (cofactorMatrix (matrixResolvent M) s t) p =
      X ^ (p.list.length - 1) * C (pathMatrixWeight M p) := by
  let S := p.list.toFinset
  have ht : t ∈ S := by
    change t ∈ p.list.toFinset
    have hmem := List.getLast_mem p.nonempty
    rw [p.last_eq, p.last_is_t] at hmem
    simpa using hmem
  have h₂series : ∀ x : R⟦X⟧, x + x = 0 := by
    intro x
    apply PowerSeries.ext
    intro n
    simpa only [map_add, map_zero] using h₂ (PowerSeries.coeff n x)
  have hneg : ∀ x : R⟦X⟧, -x = x := by
    intro x
    have h := h₂series x
    calc
      -x = -(x + x) + x := by abel
      _ = x := by rw [h]; simp
  have hlast :
      cofactorMatrix (matrixResolvent M) s t
        (cycleOfPath p t) t = 1 := by
    have hcycle : cycleOfPath p t = s := by
      calc
        cycleOfPath p t = cycleOfPath p p.last :=
          congrArg (cycleOfPath p) p.last_is_t.symm
        _ = p.first := cycleOfPath_last p
        _ = s := p.first_is_s
    simp [cofactorMatrix, hcycle, Matrix.updateRow_apply]
  have hfactor (x : V) (hx : x ∈ S.erase t) :
      cofactorMatrix (matrixResolvent M) s t
          (cycleOfPath p x) x =
        X * C (M x (cycleOfPath p x)) := by
    have hxmem : x ∈ p.list := by
      have hx' : x ∈ S := (Finset.mem_erase.mp hx).2
      simpa [S] using hx'
    have hxt : x ≠ t := (Finset.mem_erase.mp hx).1
    have hrow : cycleOfPath p x ≠ s := by
      intro heq
      have htrow : cycleOfPath p t = s := by
        calc
          cycleOfPath p t = cycleOfPath p p.last :=
            congrArg (cycleOfPath p) p.last_is_t.symm
          _ = p.first := cycleOfPath_last p
          _ = s := p.first_is_s
      exact hxt ((cycleOfPath p).injective (heq.trans htrow.symm))
    have hneq : x ≠ cycleOfPath p x := by
      exact Ne.symm ((List.formPerm_apply_mem_ne_self_iff (l := p.list)
        p.nodup x hxmem).2 p.length)
    rw [cofactorMatrix]
    simp only [Matrix.updateRow_apply, if_neg hrow, Matrix.transpose_apply]
    rw [resolvent_apply_offdiag M hneq, hneg]
  unfold cycleMonomial
  change (∏ x ∈ S,
    cofactorMatrix (matrixResolvent M) s t (cycleOfPath p x) x) = _
  rw [← Finset.mul_prod_erase S
    (fun x => cofactorMatrix (matrixResolvent M) s t (cycleOfPath p x) x) ht]
  rw [hlast, one_mul]
  have hprod :
      (∏ x ∈ S.erase t,
        cofactorMatrix (matrixResolvent M) s t (cycleOfPath p x) x) =
        ∏ x ∈ S.erase t, X * C (M x (cycleOfPath p x)) := by
    apply Finset.prod_congr rfl
    exact hfactor
  rw [hprod]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_erase_of_mem ht, ← map_prod]
  simp [S, pathMatrixWeight, List.toFinset_card_of_nodup p.nodup]

end
end TwoDoorsProof
