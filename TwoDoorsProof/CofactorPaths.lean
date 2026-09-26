import TwoDoorsProof.PermutationTerms

namespace TwoDoorsProof

open Matrix

noncomputable section

variable {V R : Type*} [DecidableEq V] [Fintype V] [CommRing R]
variable {s t : V}

def cofactorMatrix (A : Matrix V V R) (s t : V) : Matrix V V R :=
  Aᵀ.updateRow s (Pi.single t 1)

theorem cofactorMatrix_det (A : Matrix V V R) (s t : V) :
    (cofactorMatrix A s t).det = A.adjugate s t := by
  rw [cofactorMatrix, ← Matrix.adjugate_apply]
  have h := Matrix.adjugate_transpose A
  exact congrArg (fun B : Matrix V V R => B t s) h.symm

theorem cofactorMatrix_monomial_zero
    (A : Matrix V V R) (σ : Equiv.Perm V) (h : σ t ≠ s) :
    permMonomial (cofactorMatrix A s t) σ = 0 := by
  let i := σ⁻¹ s
  have hi : i ≠ t := by
    intro hit
    have hs : σ i = s := σ.apply_symm_apply s
    exact h (hit ▸ hs)
  unfold permMonomial
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  have hs : σ i = s := σ.apply_symm_apply s
  simp [cofactorMatrix, Matrix.updateRow_apply, hs, Pi.single_apply, hi]

theorem cofactorMatrix_submatrix
    (A : Matrix V V R) (p : DirectedPathList s t) :
    (cofactorMatrix A s t).submatrix
        (fun x : {x : V // x ∉ p.list} => (x : V))
        (fun x : {x : V // x ∉ p.list} => (x : V)) =
      (A.submatrix
        (fun x : {x : V // x ∉ p.list} => (x : V))
        (fun x : {x : V // x ∉ p.list} => (x : V)))ᵀ := by
  ext i j
  have hs : s ∈ p.list := by
    have hhead : p.list.head p.nonempty ∈ p.list := List.head_mem p.nonempty
    rw [p.first_eq, p.first_is_s] at hhead
    exact hhead
  have hne : (i : V) ≠ s := by
    intro heq
    apply i.property
    simpa only [heq] using hs
  simp [cofactorMatrix, Matrix.submatrix_apply,
    Matrix.updateRow_apply, hne, Matrix.transpose_apply]

theorem cofactor_path_complement_expansion
    (h₂ : ∀ x : R, x + x = 0) (A : Matrix V V R)
    (hst : s ≠ t) :
    A.adjugate s t =
      ∑ p : DirectedPathList s t,
        cycleMonomial (cofactorMatrix A s t) p *
          (A.submatrix
            (fun x : {x : V // x ∉ p.list} => (x : V))
            (fun x : {x : V // x ∉ p.list} => (x : V))).det := by
  rw [← cofactorMatrix_det A s t,
    det_eq_perm_sum_charTwo h₂]
  have hfilter :
      (∑ σ : Equiv.Perm V, permMonomial (cofactorMatrix A s t) σ) =
        ∑ σ : markedPerm s t,
          permMonomial (cofactorMatrix A s t) σ.1 := by
    classical
    calc
      (∑ σ : Equiv.Perm V, permMonomial (cofactorMatrix A s t) σ) =
          ∑ σ ∈ (Finset.univ.filter fun σ : Equiv.Perm V => σ t = s),
            permMonomial (cofactorMatrix A s t) σ := by
            symm
            apply Finset.sum_subset (Finset.filter_subset _ _)
            intro σ hσ hnot
            exact cofactorMatrix_monomial_zero A σ
              (fun h => hnot (Finset.mem_filter.mpr ⟨hσ, h⟩))
      _ = ∑ σ : markedPerm s t,
          permMonomial (cofactorMatrix A s t) σ.1 := by
            rw [← Finset.sum_subtype_eq_sum_filter, Finset.subtype_univ]
  rw [hfilter, marked_perm_sum_eq_path_complement_det h₂
    (cofactorMatrix A s t) hst]
  apply Fintype.sum_congr
  intro p
  congr 1
  rw [cofactorMatrix_submatrix A p, Matrix.det_transpose]

end
end TwoDoorsProof
