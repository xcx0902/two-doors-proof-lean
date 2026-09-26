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

theorem pathMatrixWeight_eq_dropLast_prod
    (M : Matrix V V R) (p : DirectedPathList s t) :
    pathMatrixWeight M p =
      (p.list.dropLast.map (fun x => M x (cycleOfPath p x))).prod := by
  have hnodup : p.list.dropLast.Nodup :=
    p.list.dropLast_prefix.nodup p.nodup
  have hlast_not : p.last ∉ p.list.dropLast := by
    intro hlast
    have hnodup' : (p.list.dropLast ++ [p.last]).Nodup := by
      rw [← p.last_eq, p.list.dropLast_append_getLast p.nonempty]
      simpa [p.last_eq] using p.nodup
    exact (List.nodup_append.mp hnodup').2.2 p.last hlast
      p.last (by simp)
      rfl
  have hfin :
      p.list.dropLast.toFinset = p.list.toFinset.erase t := by
    ext x
    rw [Finset.mem_erase]
    simp only [List.mem_toFinset]
    constructor
    · intro hx
      exact ⟨by
        intro heq
        subst x
        apply hlast_not
        rw [p.last_is_t]
        exact hx, p.list.dropLast_subset hx⟩
    · rintro ⟨hne, hx⟩
      have hne_last : x ≠ p.last := by
        intro hlastx
        apply hne
        exact hlastx.trans p.last_is_t
      have hne_getLast : x ≠ p.list.getLast p.nonempty := by
        intro hlastx
        apply hne_last
        exact hlastx.trans p.last_eq
      exact List.mem_dropLast_of_mem_of_ne_getLast hx hne_getLast
  rw [pathMatrixWeight, ← hfin]
  let f : V → R := fun x => M x (cycleOfPath p x)
  have hpow :
      (∏ x ∈ p.list.dropLast.toFinset, f x) =
        ∏ x ∈ p.list.dropLast.toFinset, f x ^ p.list.dropLast.count x := by
    apply Finset.prod_congr rfl
    intro x hx
    have hxl : x ∈ p.list.dropLast := List.mem_toFinset.mp hx
    rw [hnodup.count]
    simp [hxl]
  calc
    (∏ x ∈ p.list.dropLast.toFinset, M x (cycleOfPath p x)) =
        ∏ x ∈ p.list.dropLast.toFinset, f x := by rfl
    _ = ∏ x ∈ p.list.dropLast.toFinset,
        f x ^ p.list.dropLast.count x := hpow
    _ = (p.list.dropLast.map f).prod :=
      (Finset.prod_list_map_count p.list.dropLast f).symm

theorem formPerm_dropLast_map_eq_zipWith
  (l : List V) (hne : l ≠ []) (hnodup : l.Nodup) :
    l.dropLast.map (fun x => s(x, l.formPerm x)) =
      List.zipWith (fun x y => s(x, y)) l l.tail := by
  apply List.ext_getElem
  · simp [List.length_zipWith, List.length_dropLast]
  · intro i hi₁ hi₂
    have hi_drop : i < l.dropLast.length := by
      simpa using hi₁
    have hi : i + 1 < l.length := by
      simp [List.length_dropLast] at hi_drop
      omega
    have hmem : l[i] ∈ l := List.getElem_mem hi.le
    rw [List.getElem_map, List.getElem_dropLast hi_drop,
      List.formPerm_apply_mem_eq_next hnodup l[i] hmem,
      List.next_getElem l hnodup i hi.le,
      List.getElem_zipWith, List.getElem_tail]
    simp [Nat.mod_eq_of_lt hi]

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
