import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps

/-!
# The contracted dual graph

The planar grid-to-dual correspondence is upstream of this module. Here `V` is
the set of contracted dual vertices, `s` and `t` are the two boundary vertices,
and `a` and `b` are the (undirected) special edges. `F` is the set of ordinary
doors that have been blocked. Existing walls have already been contracted.
-/

namespace TwoDoorsProof

open SimpleGraph

variable {V : Type*} (s t : V) (a b : Sym2 V)

def selected (F : Set (Sym2 V)) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (F ∪ {a, b})

def withoutB (F : Set (Sym2 V)) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (F ∪ {a})

def withoutA (F : Set (Sym2 V)) : SimpleGraph V :=
  SimpleGraph.fromEdgeSet (F ∪ {b})

/-- The three non-reachability/reachability conditions on the dual. The
condition without either special edge follows by monotonicity. -/
def Valid (F : Set (Sym2 V)) : Prop :=
  ¬ (withoutB a F).Reachable s t ∧
  ¬ (withoutA b F).Reachable s t ∧
  (selected a b F).Reachable s t

private theorem reachable_of_edges_subset {H K : SimpleGraph V}
    (p : H.Walk s t) (h : ∀ e ∈ p.edges, e ∈ K.edgeSet) :
    K.Reachable s t :=
  ⟨p.transfer K h⟩

/-- Every simple path witnessing a valid blocking configuration uses both
special edges. In particular, feasibility implies a target simple path. -/
theorem valid_has_target_path (F : Set (Sym2 V)) (h : Valid s t a b F) :
    ∃ p : (selected a b F).Walk s t,
      p.IsPath ∧ a ∈ p.edges ∧ b ∈ p.edges := by
  obtain ⟨p, hp⟩ := h.2.2.exists_isPath
  refine ⟨p, hp, ?_, ?_⟩
  · by_contra ha
    apply h.2.1
    apply reachable_of_edges_subset s t p
    intro e he
    have he' : e ∈ (selected a b F).edgeSet := p.edges_subset_edgeSet he
    obtain ⟨hm, hnd⟩ : e ∈ F ∪ {a, b} ∧ e ∉ Sym2.diagSet := by
      simpa [selected] using he'
    rw [withoutA, SimpleGraph.edgeSet_fromEdgeSet]
    refine ⟨?_, hnd⟩
    rcases hm with hF | hA | hB
    · exact Or.inl hF
    · exact False.elim (ha (hA ▸ he))
    · exact Or.inr (by simp [hB])
  · by_contra hb
    apply h.1
    apply reachable_of_edges_subset s t p
    intro e he
    have he' : e ∈ (selected a b F).edgeSet := p.edges_subset_edgeSet he
    obtain ⟨hm, hnd⟩ : e ∈ F ∪ {a, b} ∧ e ∉ Sym2.diagSet := by
      simpa [selected] using he'
    rw [withoutB, SimpleGraph.edgeSet_fromEdgeSet]
    refine ⟨?_, hnd⟩
    rcases hm with hF | hA | hB
    · exact Or.inl hF
    · exact Or.inr (by simp [hA])
    · exact False.elim (hb (hB ▸ he))

end TwoDoorsProof
