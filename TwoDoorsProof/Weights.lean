import TwoDoorsProof.Shortest
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.CharP.Two
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Data.ZMod.Basic

namespace TwoDoorsProof

open SimpleGraph

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

/-- A simple path with fixed endpoints is determined by its multiset of
undirected edges. -/
theorem path_eq_of_edges_perm {u v : V} (p q : G.Walk u v)
    (hp : p.IsPath) (hq : q.IsPath) (he : p.edges.Perm q.edges) : p = q := by
  induction p with
  | nil =>
      cases q with
      | nil => rfl
      | cons hadj rest =>
          have hlen := he.length_eq
          simp [Walk.edges_cons] at hlen
  | @cons u w v hadj rest ih =>
      cases q with
      | nil =>
          have hlen := he.length_eq
          simp [Walk.edges_cons] at hlen
      | @cons u w' v hadj' rest' =>
          have hmem : s(u, w) ∈ (Walk.cons hadj' rest').edges :=
            he.mem_iff.mp (by simp [Walk.edges_cons])
          have hw : w = w' := by
            have h := hq.eq_snd_of_mem_edges hmem
            simpa [Walk.snd_cons] using h
          subst w'
          have hrest : rest.edges.Perm rest'.edges := by
            apply List.Perm.cons_inv
            simpa only [Walk.edges_cons] using he
          have heq : rest = rest' :=
            ih rest' (Walk.cons_isPath_iff hadj rest |>.mp hp).1
              (Walk.cons_isPath_iff hadj' rest' |>.mp hq).1 hrest
          subst rest'
          rfl

def edgeCode {u v : V} (p : G.Walk u v) : Sym2 V →₀ ℕ :=
  Multiset.toFinsupp (p.edges : Multiset (Sym2 V))

theorem edgeCode_apply {u v : V} (p : G.Walk u v) (e : Sym2 V) :
    edgeCode p e = p.edges.count e := by
  simp [edgeCode, Multiset.toFinsupp_apply]

theorem edgeCode_injective_on_paths {u v : V} {p q : G.Walk u v}
    (hp : p.IsPath) (hq : q.IsPath) (he : edgeCode p = edgeCode q) :
    p = q := by
  apply path_eq_of_edges_perm p q hp hq
  apply List.perm_iff_count.mpr
  intro e
  have h := congrArg (fun m : Sym2 V →₀ ℕ => m e) he
  simpa only [edgeCode_apply] using h

theorem walkWeight_X_eq_monomial {u v : V} {R : Type*} [CommRing R]
    (p : G.Walk u v) :
    walkWeight G u v (MvPolynomial.X : Sym2 V → MvPolynomial (Sym2 V) R) p =
      MvPolynomial.monomial (edgeCode p) 1 := by
  unfold walkWeight
  rw [Finset.prod_list_map_count]
  have hs : (edgeCode p).support = p.edges.toFinset := by
    simp [edgeCode, Multiset.toFinsupp_support]
  rw [← hs]
  simpa only [edgeCode_apply] using
    (MvPolynomial.prod_X_pow_eq_monomial (s := edgeCode p) (R := R))

theorem pathSum_X_ne_zero_of_mem
    [Fintype V] [DecidableRel G.Adj]
    (u v : V) (a b : Sym2 V) (d : ℕ)
    (p : G.Walk u v) (hp : p ∈ targetPaths G u v a b d) :
    pathSum' (G := G) (s := u) (t := v) (a := a) (b := b)
      (MvPolynomial.X : Sym2 V → MvPolynomial (Sym2 V) (ZMod 2)) d ≠ 0 := by
  have hpath : p.IsPath := (Finset.mem_filter.mp hp).2
  intro hzero
  have hcoeff := congrArg
    (fun Q : MvPolynomial (Sym2 V) (ZMod 2) => Q.coeff (edgeCode p)) hzero
  have hsum :
      (pathSum' (G := G) (s := u) (t := v) (a := a) (b := b)
          (MvPolynomial.X : Sym2 V → MvPolynomial (Sym2 V) (ZMod 2)) d).coeff
        (edgeCode p) = 1 := by
    unfold pathSum'
    rw [MvPolynomial.coeff_sum]
    have hsingle :
        ∑ q ∈ targetPaths G u v a b d,
            (walkWeight G u v
                (MvPolynomial.X : Sym2 V → MvPolynomial (Sym2 V) (ZMod 2)) q).coeff
              (edgeCode p) =
          1 := by
      rw [Finset.sum_eq_single p]
      · rw [walkWeight_X_eq_monomial, MvPolynomial.coeff_monomial]
        simp
      · intro q hq hne
        have hqpath : q.IsPath := (Finset.mem_filter.mp hq).2
        have hcode : edgeCode q ≠ edgeCode p := by
          intro heq
          exact hne (edgeCode_injective_on_paths hqpath hpath heq)
        rw [walkWeight_X_eq_monomial, MvPolynomial.coeff_monomial]
        simp [hcode]
      · exact fun hnot => False.elim (hnot hp)
    exact hsingle
  rw [hsum] at hcoeff
  exact one_ne_zero hcoeff

theorem pathSum_X_ne_zero_of_shortest
    [Fintype V] [DecidableRel G.Adj]
    {u v : V} {a b : Sym2 V} {d : ℕ}
    (hshort : IsShortestTargetPath (G := G) (s := u) (t := v)
      (a := a) (b := b) d) :
    pathSum' (G := G) (s := u) (t := v) (a := a) (b := b)
      (MvPolynomial.X : Sym2 V → MvPolynomial (Sym2 V) (ZMod 2)) d ≠ 0 := by
  obtain ⟨p, ⟨hpath, ha, hb⟩, hlen, _⟩ := hshort
  have hwalk : p ∈ G.finsetWalkLength d u v := by
    have hset : p ∈ (G.finsetWalkLength d u v : Set (G.Walk u v)) := by
      rw [SimpleGraph.coe_finsetWalkLength_eq]
      exact hlen
    exact Finset.mem_coe.mp hset
  have hp : p ∈ targetPaths G u v a b d := by
    apply Finset.mem_filter.mpr
    refine ⟨?_, hpath⟩
    apply Finset.mem_filter.mpr
    exact ⟨hwalk, ha, hb⟩
  exact pathSum_X_ne_zero_of_mem u v a b d p hp

private theorem polynomial_add_self_zero (x : MvPolynomial (Sym2 V) (ZMod 2)) :
    x + x = 0 := by
  ext m
  simp [CharTwo.add_self_eq_zero]

theorem first_nonzero_of_concrete_palindrome_reversal
    [Fintype V] [DecidableRel G.Adj]
    {u v : V} {a b : Sym2 V} {dStar : ℕ}
    (hshort : IsShortestTargetPath (G := G) (s := u) (t := v)
      (a := a) (b := b) dStar) :
    (∀ d, d < dStar →
      walkSum' (G := G) (s := u) (t := v) (a := a) (b := b)
        (MvPolynomial.X : Sym2 V → MvPolynomial (Sym2 V) (ZMod 2)) d = 0) ∧
      walkSum' (G := G) (s := u) (t := v) (a := a) (b := b)
        (MvPolynomial.X : Sym2 V → MvPolynomial (Sym2 V) (ZMod 2))
        dStar ≠ 0 := by
  obtain ⟨p, hpath, hlen, hmin⟩ := hshort
  have hshort' : IsShortestTargetPath (G := G) (s := u) (t := v)
      (a := a) (b := b) dStar := ⟨p, hpath, hlen, hmin⟩
  have hprevious : ∀ d, d < dStar →
      ¬ ∃ q : G.Walk u v,
        IsTargetPath (a := a) (b := b) q ∧ q.length = d := by
    intro d hd ⟨q, hq, hlength⟩
    have := hmin q hq
    omega
  exact first_nonzero_of_palindrome_reversal
    (fun x => polynomial_add_self_zero x)
    (MvPolynomial.X : Sym2 V → MvPolynomial (Sym2 V) (ZMod 2))
    dStar hprevious (pathSum_X_ne_zero_of_shortest hshort')
    (palindrome_reversal_certificate_of_minimal _ dStar hmin)

theorem walkSum_X_eq_zero_of_no_target_path
    [Fintype V] [DecidableRel G.Adj]
    {u v : V} {a b : Sym2 V}
    (hno : ¬ ∃ p : G.Walk u v,
      IsTargetPath (a := a) (b := b) p)
    (d : ℕ) :
    walkSum' (G := G) (s := u) (t := v) (a := a) (b := b)
      (MvPolynomial.X : Sym2 V → MvPolynomial (Sym2 V) (ZMod 2)) d = 0 := by
  have hmin : ∀ q : G.Walk u v,
      IsTargetPath (a := a) (b := b) q → d ≤ q.length :=
    fun q hq => False.elim (hno ⟨q, hq⟩)
  rw [walkSum_eq_pathSum_of_certificate
    (fun x => polynomial_add_self_zero x)
    (MvPolynomial.X : Sym2 V → MvPolynomial (Sym2 V) (ZMod 2)) d
    ((palindrome_reversal_certificate_of_minimal _ d hmin).layer d le_rfl)]
  exact pathSum'_eq_zero_of_no_target_path _ d (fun ⟨q, hq, _⟩ => hno ⟨q, hq⟩)

end TwoDoorsProof
