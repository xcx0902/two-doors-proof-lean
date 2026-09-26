import TwoDoorsProof.DeterminantPaths
import Mathlib.GroupTheory.Perm.List
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.GroupTheory.Perm.Cycle.Factors

namespace TwoDoorsProof

open Equiv Equiv.Perm

noncomputable section

variable {V : Type*} [DecidableEq V] [Fintype V]
variable {s t : V}

/-!
The permutation part of the cofactor expansion.

The type `DirectedPathList s t` records the nontrivial cycle containing
`s`, with its last vertex equal to `t`.  A permutation on the complement
of this list can be extended by fixing the list pointwise.  The product
of the cycle permutation and that extension is then the unique permutation
whose distinguished cycle is the prescribed path and whose complementary
part is the chosen permutation.
-/

structure DirectedPathList (s t : V) where
  list : List V
  nonempty : list ≠ []
  nodup : list.Nodup
  length : 2 ≤ list.length
  first : V
  last : V
  first_eq : list.head nonempty = first
  last_eq : list.getLast nonempty = last
  first_is_s : first = s
  last_is_t : last = t

def cycleOfPath (p : DirectedPathList s t) : Equiv.Perm V :=
  p.list.formPerm

abbrev complementPerm (p : DirectedPathList s t) :=
  Equiv.Perm {x : V // x ∉ p.list}

def extendComplement (p : DirectedPathList s t)
    (τ : complementPerm p) : Equiv.Perm V := by
  classical
  change Equiv.Perm {x : V // x ∉ p.list} at τ
  exact Equiv.Perm.ofSubtype τ

def pathComplementPerm (p : DirectedPathList s t) (τ : complementPerm p) :
    Equiv.Perm V :=
  cycleOfPath p * extendComplement p τ

theorem cycleOfPath_apply_of_not_mem
    (p : DirectedPathList s t) {x : V} (hx : x ∉ p.list) :
    cycleOfPath p x = x := by
  exact List.formPerm_apply_of_notMem (l := p.list) hx

theorem extendComplement_apply_of_mem
    (p : DirectedPathList s t) (τ : complementPerm p)
    {x : V} (hx : x ∈ p.list) :
    extendComplement p τ x = x := by
  classical
  change Equiv.Perm {x : V // x ∉ p.list} at τ
  change Equiv.Perm.ofSubtype τ x = x
  exact Equiv.Perm.ofSubtype_apply_of_not_mem τ (by simpa using hx)

theorem extendComplement_apply_of_not_mem
    (p : DirectedPathList s t) (τ : complementPerm p)
    {x : V} (hx : x ∉ p.list) :
    extendComplement p τ x = τ ⟨x, hx⟩ := by
  classical
  change Equiv.Perm {x : V // x ∉ p.list} at τ
  unfold extendComplement
  simp only [id_eq]
  rw [Equiv.Perm.ofSubtype_apply_of_mem τ hx]

theorem cycleOfPath_apply_mem
    (p : DirectedPathList s t) {x : V} (hx : x ∈ p.list) :
    cycleOfPath p x = p.list.next x hx := by
  exact @List.formPerm_apply_mem_eq_next V _ p.list p.nodup x hx

theorem cycleOfPath_last (p : DirectedPathList s t) :
    cycleOfPath p p.last = p.first := by
  cases hl : p.list with
  | nil =>
      exact (p.nonempty hl).elim
  | cons x xs =>
      have hlast : (x :: xs).getLast (by simp) = p.last := by
        simpa [hl] using p.last_eq
      have hfirst : (x :: xs).head (by simp) = p.first := by
        simpa [hl] using p.first_eq
      change p.list.formPerm p.last = p.first
      rw [hl, ← hlast, ← hfirst]
      exact List.formPerm_apply_getLast x xs

theorem pathComplementPerm_apply_mem
    (p : DirectedPathList s t) (τ : complementPerm p)
    {x : V} (hx : x ∈ p.list) :
    pathComplementPerm p τ x = cycleOfPath p x := by
  rw [pathComplementPerm, Equiv.Perm.mul_apply,
    extendComplement_apply_of_mem p τ hx]

theorem pathComplementPerm_apply_of_not_mem
    (p : DirectedPathList s t) (τ : complementPerm p)
    {x : V} (hx : x ∉ p.list) :
    pathComplementPerm p τ x = τ ⟨x, hx⟩ := by
  rw [pathComplementPerm, Equiv.Perm.mul_apply,
    extendComplement_apply_of_not_mem p τ hx]
  apply cycleOfPath_apply_of_not_mem
  exact (τ ⟨x, hx⟩).property

private theorem cycleOfPath_support (p : DirectedPathList s t) :
    (cycleOfPath p).support = p.list.toFinset := by
  ext x
  by_cases hx : x ∈ p.list
  · rw [Equiv.Perm.mem_support]
    constructor
    · intro _
      simpa using hx
    · intro _
      exact (List.formPerm_apply_mem_ne_self_iff (l := p.list)
        p.nodup x hx).2 p.length
  · rw [Equiv.Perm.mem_support, cycleOfPath_apply_of_not_mem p hx]
    simp [hx]

private theorem extendComplement_disjoint
    (p : DirectedPathList s t) (τ : complementPerm p) :
    Disjoint (cycleOfPath p) (extendComplement p τ) := by
  rw [Equiv.Perm.disjoint_iff_disjoint_support, cycleOfPath_support,
    Finset.disjoint_left]
  intro x hx hsupport
  have hmem : x ∈ p.list := by simpa using hx
  exact (Equiv.Perm.mem_support.mp hsupport)
    (extendComplement_apply_of_mem p τ hmem)

theorem pathComplementPerm_cycle
    (p : DirectedPathList s t) (τ : complementPerm p) :
    (pathComplementPerm p τ).cycleOf p.first = cycleOfPath p := by
  classical
  have hfirst_mem : p.first ∈ p.list := by
    rw [← p.first_eq]
    exact List.head_mem p.nonempty
  have hfirst_ne : cycleOfPath p p.first ≠ p.first := by
    rw [← p.first_eq]
    exact (List.formPerm_apply_mem_ne_self_iff (l := p.list)
      p.nodup _ (List.head_mem p.nonempty)).2 p.length
  have hcycle :
      (cycleOfPath p).cycleOf p.first = cycleOfPath p :=
    (List.isCycle_formPerm p.nodup p.length).cycleOf_eq hfirst_ne
  change (cycleOf (cycleOfPath p * extendComplement p τ) p.first) =
    cycleOfPath p
  rw [cycleOf_mul_of_apply_right_eq_self
    (extendComplement_disjoint p τ).commute p.first
    (extendComplement_apply_of_mem p τ hfirst_mem), hcycle]

theorem pathComplementPerm_toList
    (p : DirectedPathList s t) (τ : complementPerm p) :
    (pathComplementPerm p τ).toList p.first = p.list := by
  have hpos : 0 < p.list.length := by
    exact Nat.lt_of_lt_of_le (by decide) p.length
  have hcard :
      (cycleOfPath p).support.card = p.list.length := by
    rw [cycleOfPath_support p, List.toFinset_card_of_nodup p.nodup]
  have hpow :
      ∀ n (hn : n < p.list.length),
        (pathComplementPerm p τ ^ n) p.first =
          p.list[n]'hn := by
    intro n
    induction n with
    | zero =>
        intro hn
        have hfirst : p.list[0]'hn = p.first := by
          exact (List.getElem_zero hpos).trans p.first_eq
        simpa [hfirst]
    | succ n ih =>
        intro hn
        rw [pow_succ', Equiv.Perm.mul_apply, ih (by omega)]
        have hmem : p.list[n] ∈ p.list := List.getElem_mem (by omega)
        rw [pathComplementPerm_apply_mem p τ hmem]
        simpa [cycleOfPath, Nat.mod_eq_of_lt (by omega)] using
          (List.formPerm_apply_getElem p.list p.nodup n (by omega))
  unfold Equiv.Perm.toList
  rw [pathComplementPerm_cycle p τ]
  apply List.ext_getElem?
  intro n
  by_cases hn : n < p.list.length
  · have hn' : n < (List.iterate (pathComplementPerm p τ)
        p.first (cycleOfPath p).support.card).length := by
      simpa [List.length_iterate, hcard] using hn
    rw [List.getElem?_eq_getElem hn', List.getElem?_eq_getElem hn,
      List.getElem_iterate]
    rw [← Equiv.Perm.coe_pow,
      hpow n (by simpa [List.length_iterate, hcard] using hn')]
  · have hn' :
        (List.iterate (pathComplementPerm p τ)
          p.first (cycleOfPath p).support.card).length ≤ n := by
      simpa [List.length_iterate, hcard] using hn
    have hnle : p.list.length ≤ n := Nat.le_of_not_gt hn
    rw [List.getElem?_eq_none hnle, List.getElem?_eq_none hn']

private theorem sameCycle_toList_iff
    (σ : Equiv.Perm V) (s : V) {x : V} :
    σ x ∈ σ.toList s ↔ x ∈ σ.toList s := by
  rw [Equiv.Perm.mem_toList_iff, Equiv.Perm.mem_toList_iff]
  constructor
  · rintro ⟨hsx, hsupp⟩
    exact ⟨Equiv.Perm.SameCycle.of_apply_right hsx, hsupp⟩
  · rintro ⟨hsx, hsupp⟩
    exact ⟨Equiv.Perm.SameCycle.apply_right hsx, hsupp⟩

def pathOfPerm (σ : Equiv.Perm V) (s t : V)
    (hst : s ≠ t) (hts : σ t = s) : DirectedPathList s t := by
  let hshape := marked_cycle_vertices σ s t hst hts
  let hne : σ.toList s ≠ [] := Classical.choose hshape
  let hspec := Classical.choose_spec hshape
  let hnodup : (σ.toList s).Nodup := hspec.1
  let hhead : (σ.toList s).head hne = s := hspec.2.1
  let hlast : (σ.toList s).getLast hne = t := hspec.2.2
  exact
    { list := σ.toList s
      nonempty := hne
      nodup := hnodup
      length := marked_cycle_length σ s t hst hts
      first := s
      last := t
      first_eq := hhead
      last_eq := hlast
      first_is_s := rfl
      last_is_t := rfl }

def restrictedPerm (σ : Equiv.Perm V) (s t : V)
    (hst : s ≠ t) (hts : σ t = s) :
    complementPerm (pathOfPerm σ s t hst hts) := by
  classical
  let p := pathOfPerm σ s t hst hts
  change Equiv.Perm {x : V // x ∉ σ.toList s}
  refine σ.subtypePerm ?_
  intro x
  exact not_congr (sameCycle_toList_iff σ s)

theorem restrictedPerm_apply
    (σ : Equiv.Perm V) (s t : V) (hst : s ≠ t) (hts : σ t = s)
    {x : V} (hx : x ∉ (pathOfPerm σ s t hst hts).list) :
    ((restrictedPerm σ s t hst hts) ⟨x, hx⟩ : V) = σ x := by
  have h :=
    Equiv.Perm.subtypePerm_apply σ
      (fun y => not_congr (sameCycle_toList_iff σ s))
      (⟨x, hx⟩ : {x : V // x ∉ (pathOfPerm σ s t hst hts).list})
  exact congrArg Subtype.val h

theorem perm_eq_pathComplement
    (σ : Equiv.Perm V) (s t : V) (hst : s ≠ t) (hts : σ t = s) :
    pathComplementPerm (pathOfPerm σ s t hst hts)
        (restrictedPerm σ s t hst hts) = σ := by
  apply Equiv.ext
  intro x
  by_cases hx : x ∈ (pathOfPerm σ s t hst hts).list
  · rw [pathComplementPerm_apply_mem
      (pathOfPerm σ s t hst hts) (restrictedPerm σ s t hst hts) hx]
    rw [cycleOfPath_apply_mem
      (pathOfPerm σ s t hst hts) hx]
    have hx' : x ∈ σ.toList s := hx
    exact Equiv.Perm.next_toList_eq_apply σ s x hx'
  · rw [pathComplementPerm_apply_of_not_mem
      (pathOfPerm σ s t hst hts) (restrictedPerm σ s t hst hts) hx]
    exact restrictedPerm_apply σ s t hst hts hx

end
end TwoDoorsProof
