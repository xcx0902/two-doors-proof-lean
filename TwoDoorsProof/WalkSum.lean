import TwoDoorsProof.Basic
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Weighted walks and the involution cancellation lemma

An undirected edge has just one weight, independently of traversal direction.
The two special edges are each required to occur exactly once. Ordinary edges
can occur arbitrarily many times, including immediate backtracks.
-/

namespace TwoDoorsProof

open SimpleGraph

variable {V R : Type*} [DecidableEq V] [Fintype V]
  (G : SimpleGraph V) [DecidableRel G.Adj] (s t : V) (a b : Sym2 V)

def targetWalks (d : ℕ) : Finset (G.Walk s t) :=
  (G.finsetWalkLength d s t).filter fun p =>
    p.edges.count a = 1 ∧ p.edges.count b = 1

def targetPaths (d : ℕ) : Finset (G.Walk s t) :=
  (targetWalks G s t a b d).filter (·.IsPath)

def targetNonpaths (d : ℕ) : Finset (G.Walk s t) :=
  (targetWalks G s t a b d).filter (¬ ·.IsPath)

def walkWeight [CommMonoid R] (z : Sym2 V → R) (p : G.Walk s t) : R :=
  (p.edges.map z).prod

def walkSum [CommRing R] (z : Sym2 V → R) (d : ℕ) : R :=
  ∑ p ∈ targetWalks G s t a b d, walkWeight G s t z p

def pathSum [CommRing R] (z : Sym2 V → R) (d : ℕ) : R :=
  ∑ p ∈ targetPaths G s t a b d, walkWeight G s t z p

/-- Abstract parity cancellation, with exactly the four properties supplied by
the palindrome-contraction/reversal construction in the editorial. -/
theorem nonpath_sum_zero [CommRing R] (h₂ : ∀ x : R, x + x = 0)
    (z : Sym2 V → R) (d : ℕ)
    (pair : ∀ p ∈ targetNonpaths G s t a b d, G.Walk s t)
    (pair_mem : ∀ p hp, pair p hp ∈ targetNonpaths G s t a b d)
    (pair_ne : ∀ p hp, pair p hp ≠ p)
    (pair_pair : ∀ p hp, pair (pair p hp) (pair_mem p hp) = p)
    (pair_weight : ∀ p hp,
      walkWeight G s t z (pair p hp) = walkWeight G s t z p) :
    ∑ p ∈ targetNonpaths G s t a b d, walkWeight G s t z p = 0 := by
  apply Finset.sum_involution pair
  · intro p hp
    rw [pair_weight p hp]
    exact h₂ _
  · intro p hp _
    exact pair_ne p hp
  · exact pair_pair

/-- The first proof's algebraic conclusion at any length for which the
palindrome/reversal involution has been constructed. -/
theorem walkSum_eq_pathSum_of_involution [CommRing R]
    (h₂ : ∀ x : R, x + x = 0)
    (z : Sym2 V → R) (d : ℕ)
    (pair : ∀ p ∈ targetNonpaths G s t a b d, G.Walk s t)
    (pair_mem : ∀ p hp, pair p hp ∈ targetNonpaths G s t a b d)
    (pair_ne : ∀ p hp, pair p hp ≠ p)
    (pair_pair : ∀ p hp, pair (pair p hp) (pair_mem p hp) = p)
    (pair_weight : ∀ p hp,
      walkWeight G s t z (pair p hp) = walkWeight G s t z p) :
    walkSum G s t a b z d = pathSum G s t a b z d := by
  have hpart : targetWalks G s t a b d =
      targetPaths G s t a b d ∪ targetNonpaths G s t a b d := by
    ext p
    simp only [targetPaths, targetNonpaths, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hp
      by_cases hpath : p.IsPath
      · exact Or.inl ⟨hp, hpath⟩
      · exact Or.inr ⟨hp, hpath⟩
    · rintro (⟨hp, _⟩ | ⟨hp, _⟩) <;> exact hp
  have hdisj : Disjoint (targetPaths G s t a b d)
      (targetNonpaths G s t a b d) := by
    apply Finset.disjoint_left.mpr
    intro p hp hnp
    exact (Finset.mem_filter.mp hnp).2 (Finset.mem_filter.mp hp).2
  rw [walkSum, pathSum, hpart, Finset.sum_union hdisj,
    nonpath_sum_zero G s t a b h₂ z d pair pair_mem pair_ne pair_pair pair_weight, add_zero]

end TwoDoorsProof
