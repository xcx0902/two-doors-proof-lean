import TwoDoorsProof.DeterminantGenerating
import Mathlib.GroupTheory.Perm.Cycle.Concrete

namespace TwoDoorsProof

variable {V : Type*} [DecidableEq V] [Fintype V]

theorem marked_cycle_vertices
    (σ : Equiv.Perm V) (s t : V)
    (hst : s ≠ t) (hts : σ t = s) :
    ∃ hne : σ.toList s ≠ [],
      (σ.toList s).Nodup ∧
        (σ.toList s).head hne = s ∧
        (σ.toList s).getLast hne = t := by
  have hss : σ s ≠ s := by
    intro hfix
    have hts' : t = s := σ.injective (by rw [hts, hfix])
    exact hst hts'.symm
  have hs : s ∈ σ.support := Equiv.Perm.mem_support.mpr hss
  have hne : σ.toList s ≠ [] := by
    intro hnil
    exact (Equiv.Perm.toList_eq_nil_iff.mp hnil) hs
  have hnodup : (σ.toList s).Nodup := σ.nodup_toList s
  have hhead : (σ.toList s).head hne = s := by
    simpa [List.head_eq_getElem] using σ.toList_getElem_zero s hs
  have hlastmem : (σ.toList s).getLast hne ∈ σ.toList s :=
    List.getLast_mem hne
  have hlast : (σ.toList s).getLast hne = t := by
    apply σ.injective
    rw [hts, ← σ.next_toList_eq_apply s _ hlastmem,
      List.next_getLast_eq_head _ hne hnodup, hhead]
  exact ⟨hne, hnodup, hhead, hlast⟩

theorem marked_cycle_length
    (σ : Equiv.Perm V) (s t : V)
    (hst : s ≠ t) (hts : σ t = s) :
    2 ≤ (σ.toList s).length := by
  have hss : σ s ≠ s := by
    intro hfix
    have hts' : t = s := σ.injective (by rw [hts, hfix])
    exact hst hts'.symm
  exact (Equiv.Perm.two_le_length_toList_iff_mem_support).2
    (Equiv.Perm.mem_support.mpr hss)

theorem marked_cycle_path_shape
    (σ : Equiv.Perm V) (s t : V)
    (hst : s ≠ t) (hts : σ t = s) :
    ∃ (l : List V) (hne : l ≠ []), l.Nodup ∧ 2 ≤ l.length ∧
      l.head hne = s ∧ l.getLast hne = t ∧
      ∀ k (hk : k + 1 < l.length),
        σ (l[k]'(Nat.lt_trans (Nat.lt_succ_self k) hk)) =
          l[k + 1]'hk := by
  let l := σ.toList s
  have hshape := marked_cycle_vertices σ s t hst hts
  obtain ⟨hne, hnodup, hhead, hlast⟩ := hshape
  have hlen := marked_cycle_length σ s t hst hts
  refine ⟨l, hne, hnodup, hlen, ?_, ?_, ?_⟩
  · simpa [l] using hhead
  · simpa [l] using hlast
  · intro k hk
    rw [Equiv.Perm.getElem_toList, Equiv.Perm.getElem_toList]
    have hss : σ s ≠ s := by
      intro hfix
      have hts' : t = s := σ.injective (by rw [hts, hfix])
      exact hst hts'.symm
    have hs : s ∈ σ.support := Equiv.Perm.mem_support.mpr hss
    have hmem : (σ ^ k) s ∈ σ.toList s :=
      (Equiv.Perm.pow_apply_mem_toList_iff_mem_support).2 hs
    simpa [pow_succ', mul_apply] using
      (show σ ((σ ^ k) s) = (σ ^ (k + 1)) s by
        rw [pow_succ']
        rfl)

end TwoDoorsProof
