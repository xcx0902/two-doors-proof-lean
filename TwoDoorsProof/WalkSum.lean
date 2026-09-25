import TwoDoorsProof.Basic
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.List.Palindrome

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

private def AdjacentNe (l : List V) : Prop :=
  l.IsChain (fun x y => x ≠ y)

private theorem adjacentNe_of_isChain
    {l : List V} (h : l.IsChain G.Adj) :
    AdjacentNe l := by
  exact h.imp fun _ _ hadj hxy => G.loopless.irrefl _ (hxy ▸ hadj)

private theorem palindrome_length_odd_of_adjacentNe
    {l : List V} (hp : l.reverse = l)
    (ha : AdjacentNe l) (hne : l ≠ []) :
    Odd l.length := by
  have hp' : l.Palindrome := List.Palindrome.of_reverse_eq hp
  induction hp' with
  | nil => exact (hne rfl).elim
  | singleton x => simp
  | @cons_concat x l hpal ih =>
      have hnonempty : l ≠ [] := by
        intro hl
        subst l
        simpa [AdjacentNe] using ha
      have hal : AdjacentNe l := by
        simpa [AdjacentNe] using ha.tail.left_of_append
      have hmid : Odd l.length := ih hpal.reverse_eq hal hnonempty
      rcases hmid with ⟨k, hk⟩
      refine ⟨k + 1, ?_⟩
      simp [List.length_append]
      omega

private theorem palindrome_count_even_of_even_length
    {l : List V} (hp : l.reverse = l)
    (hlen : Even l.length) (e : V) :
    Even (l.count e) := by
  have hp' : l.Palindrome := List.Palindrome.of_reverse_eq hp
  induction hp' with
  | nil => simp
  | singleton x => simp at hlen
  | @cons_concat x l hpal ih =>
      have hmid : Even l.length := by
        rcases hlen with ⟨k, hk⟩
        refine ⟨k - 1, ?_⟩
        simp [List.length_append] at hk
        omega
      have hcount := ih hpal.reverse_eq hmid
      rcases hcount with ⟨k, hk⟩
      by_cases hxe : x = e
      · subst e
        refine ⟨k + 1, ?_⟩
        simp [List.count_append, hk]
        omega
      · refine ⟨k, ?_⟩
        simp [List.count_append, hxe, hk]

theorem palindrome_closed_segment_special_count_even
    {u : V} (loop : G.Walk u u)
    (hpal : loop.support.reverse = loop.support) (e : Sym2 V) :
    Even (loop.edges.count e) := by
  have hwalk : loop.reverse = loop := by
    apply Walk.ext_support
    simpa [Walk.support_reverse, hpal]
  have hedges : loop.edges.reverse = loop.edges := by
    rw [← Walk.edges_reverse, hwalk]
  have hlen : Even loop.edges.length := by
    have hodd : Odd loop.support.length :=
      palindrome_length_odd_of_adjacentNe
        (l := loop.support) hpal (adjacentNe_of_isChain (G := G) loop.isChain_adj_support)
        loop.support_ne_nil
    rcases hodd with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [SimpleGraph.Walk.length_edges]
    have hs := SimpleGraph.Walk.length_support loop
    omega
  exact palindrome_count_even_of_even_length hedges hlen e

theorem palindrome_closed_segment_cannot_contain_unique_edge
    {u : V} (loop : G.Walk u u)
    (hpal : loop.support.reverse = loop.support) (e : Sym2 V)
    (hcount : loop.edges.count e = 1) : False := by
  have heven := palindrome_closed_segment_special_count_even (G := G) loop hpal e
  rw [hcount] at heven
  rcases heven with ⟨k, hk⟩
  omega

section Flip

variable {G s t} {u : V}

/-- Reverse a closed segment in place. The same undirected edges are used,
including their multiplicities; no immediate backtrack is forbidden. -/
def flipClosed (pre : G.Walk s u) (loop : G.Walk u u)
    (suffix : G.Walk u t) : G.Walk s t :=
  (pre.append loop.reverse).append suffix

theorem flipClosed_support
    (pre : G.Walk s u) (loop : G.Walk u u) (suffix : G.Walk u t) :
    (flipClosed pre loop suffix).support =
      pre.support ++ loop.support.reverse.tail ++ suffix.support.tail := by
  simp [flipClosed, SimpleGraph.Walk.support_append, SimpleGraph.Walk.support_reverse]

theorem flipClosed_ne_of_not_palindrome
    (pre : G.Walk s u) (loop : G.Walk u u) (suffix : G.Walk u t)
    (hloop : loop.support.reverse ≠ loop.support) :
    flipClosed pre loop suffix ≠ (pre.append loop).append suffix := by
  intro h
  have hs := congrArg SimpleGraph.Walk.support h
  rw [flipClosed_support, SimpleGraph.Walk.support_append,
    SimpleGraph.Walk.support_append] at hs
  rw [List.append_assoc, List.append_assoc] at hs
  have htail :
      loop.support.reverse.tail ++ suffix.support.tail =
        loop.support.tail ++ suffix.support.tail := by
    exact List.append_right_injective pre.support hs
  have htail' : loop.support.reverse.tail = loop.support.tail :=
    List.append_left_injective suffix.support.tail htail
  apply hloop
  have htail'' : loop.reverse.support.tail = loop.support.tail := by
    simpa [SimpleGraph.Walk.support_reverse] using htail'
  calc
    loop.support.reverse = loop.reverse.support := by
      simp [SimpleGraph.Walk.support_reverse]
    _ = u :: loop.reverse.support.tail := (loop.reverse.cons_tail_support).symm
    _ = u :: loop.support.tail := by rw [htail'']
    _ = loop.support := loop.cons_tail_support

theorem flipClosed_twice (pre : G.Walk s u) (loop : G.Walk u u)
    (suffix : G.Walk u t) :
    flipClosed pre loop.reverse suffix = (pre.append loop).append suffix := by
  simp [flipClosed]

theorem flipClosed_length (pre : G.Walk s u) (loop : G.Walk u u)
    (suffix : G.Walk u t) :
    (flipClosed pre loop suffix).length =
      ((pre.append loop).append suffix).length := by
  simp [flipClosed, SimpleGraph.Walk.length_append]

theorem flipClosed_count (pre : G.Walk s u) (loop : G.Walk u u)
    (suffix : G.Walk u t) (e : Sym2 V) :
    (flipClosed pre loop suffix).edges.count e =
      ((pre.append loop).append suffix).edges.count e := by
  simp [flipClosed, List.count_append, List.count_reverse]

theorem flipClosed_weight [CommMonoid R] (z : Sym2 V → R)
    (pre : G.Walk s u) (loop : G.Walk u u)
    (suffix : G.Walk u t) :
    walkWeight G s t z (flipClosed pre loop suffix) =
      walkWeight G s t z ((pre.append loop).append suffix) := by
  simp [flipClosed, walkWeight, List.prod_append, List.prod_reverse]

end Flip

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
