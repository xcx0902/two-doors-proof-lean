import TwoDoorsProof.Marked
import Mathlib.Data.Matrix.Basic

namespace TwoDoorsProof

open SimpleGraph Matrix
open scoped Matrix

variable {V R : Type*} [DecidableEq V] [Fintype V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

def weightedAdj [Semiring R] (z : Sym2 V → R) : Matrix V V R :=
  fun u v => if G.Adj u v then z s(u, v) else 0

omit [DecidableEq V] [Fintype V] in
theorem weightedAdj_apply [Semiring R] (z : Sym2 V → R)
    (u v : V) (h : G.Adj u v) :
    weightedAdj G z u v = z s(u, v) := by
  simp [weightedAdj, h]

omit [DecidableEq V] [Fintype V] in
theorem weightedAdj_apply_of_not_adj [Semiring R] (z : Sym2 V → R)
    (u v : V) (h : ¬ G.Adj u v) :
    weightedAdj G z u v = 0 := by
  simp [weightedAdj, h]

theorem weightedAdj_pow_walks [CommSemiring R] (z : Sym2 V → R)
    (d : ℕ) (u v : V) :
    (weightedAdj G z ^ d) u v =
      ∑ p ∈ G.finsetWalkLength d u v, walkWeight G u v z p := by
  induction d generalizing u with
  | zero =>
      by_cases huv : u = v
      · subst v
        simp [SimpleGraph.finsetWalkLength, walkWeight]
      · simp [SimpleGraph.finsetWalkLength, huv]
  | succ d ih =>
      rw [pow_succ', Matrix.mul_apply]
      simp only [SimpleGraph.finsetWalkLength]
      rw [Finset.sum_biUnion]
      · simp only [Finset.sum_map]
        change (∑ j, weightedAdj G z u j * (weightedAdj G z ^ d) j v) =
          ∑ x : G.neighborSet u,
            ∑ p ∈ G.finsetWalkLength d x v,
              walkWeight G u v z (Walk.cons (show G.Adj u x from x.property) p)
        calc
          (∑ j, weightedAdj G z u j * (weightedAdj G z ^ d) j v) =
              ∑ x : G.neighborSet u,
                z s(u, x) * (weightedAdj G z ^ d) x v := by
                  simp only [weightedAdj, ite_mul, zero_mul]
                  let f : V → R := fun j =>
                    z s(u, j) * (weightedAdj G z ^ d) j v
                  change (∑ j, if G.Adj u j then f j else 0) =
                    ∑ x : G.neighborSet u, f x
                  calc
                    _ = ∑ j ∈ ({j | G.Adj u j} : Set V).toFinset, f j := by
                      simp [Finset.sum_filter]
                    _ = ∑ x : {j // G.Adj u j}, f x :=
                      Finset.sum_toFinset_eq_subtype (fun j => G.Adj u j) f
                    _ = _ := rfl
          _ = ∑ x : G.neighborSet u,
                z s(u, x) *
                  ∑ p ∈ G.finsetWalkLength d x v, walkWeight G x v z p := by
                    apply Finset.sum_congr rfl
                    intro x hx
                    rw [ih x]
          _ = ∑ x : G.neighborSet u,
                ∑ p ∈ G.finsetWalkLength d x v,
                  walkWeight G u v z (Walk.cons x.property p) := by
                    apply Finset.sum_congr rfl
                    intro x hx
                    rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro p hp
                    have hadj : G.Adj u x := x.property
                    change z s(u, (x : V)) * (p.edges.map z).prod =
                      ((Walk.cons hadj p).edges.map z).prod
                    rw [Walk.edges_cons]
                    rfl
      · intro x hx y hy hxy
        apply Finset.disjoint_left.mpr
        intro p hpx hpy
        obtain ⟨p₁, hp₁, rfl⟩ := Finset.mem_map.mp hpx
        obtain ⟨p₂, hp₂, heq⟩ := Finset.mem_map.mp hpy
        have hxy' : (x : V) = y := by
          have h := congrArg Walk.snd heq
          change (Walk.cons y.property p₂).snd =
            (Walk.cons x.property p₁).snd at h
          rw [Walk.snd_cons p₂ y.property,
            Walk.snd_cons p₁ x.property] at h
          exact h.symm
        exact hxy (Subtype.ext hxy')

theorem marked_matrix_pow_coefficient [CommRing R]
    (u v : V) (a b : Sym2 V) (hab : a ≠ b)
    (z : Sym2 V → R) (d : ℕ) :
    markedCoeff ((weightedAdj G (markedEdgeWeight a b z) ^ d) u v) =
      walkSum G u v a b z d := by
  rw [weightedAdj_pow_walks G (markedEdgeWeight a b z) d u v]
  exact marked_walk_sum_coefficient (G := G) u v a b hab z d

end TwoDoorsProof
