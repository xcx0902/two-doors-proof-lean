import TwoDoorsProof.Palindrome

namespace TwoDoorsProof

open SimpleGraph

variable {V : Type*} [DecidableEq V] [Fintype V]
  {G : SimpleGraph V} [DecidableRel G.Adj] {s t : V}

private theorem scanNonpal_none_unique_head {l : List V}
    (hlen : 0 < l.length)
    (hunique : lastIndex? l[0] (l.drop 1) = none) :
    scanNonpal l 0 = none ↔ scanNonpal (l.drop 1) 0 = none := by
  have hshift := scanNonpal_none_drop l 1
  conv_lhs => rw [scanNonpal.eq_1]
  simp only [hlen, ↓reduceDIte, Nat.zero_add, List.drop_zero]
  rw [hunique]
  exact hshift

private theorem scanNonpal_none_contract {l : List V} {k : ℕ}
    (hlen : 0 < l.length) (hq : 1 + k < l.length)
    (hidx : lastIndex? l[0] (l.drop 1) = some k)
    (hpal : (intervalSegment l 0 (1 + k)).reverse =
      intervalSegment l 0 (1 + k))
    (hscan : scanNonpal l 0 = none) :
    scanNonpal (l.drop (1 + k)) 0 = none := by
  have hi := lastIndex?_some_iff.mp hidx
  have hrec : scanNonpal l (1 + k + 1) = none := by
    rw [scanNonpal.eq_1] at hscan
    simp only [hlen, ↓reduceDIte, Nat.zero_add, List.drop_zero, hidx] at hscan
    have hpali :
        (List.take (1 + k - 0 + 1) (List.drop 0 l)).reverse =
          List.take (1 + k - 0 + 1) (List.drop 0 l) := by
      simpa only [intervalSegment] using hpal
    simp only [List.drop_zero] at hpali
    rw [if_pos hpali] at hscan
    simpa using hscan
  have hlen' : 0 < (l.drop (1 + k)).length := by
    simp only [List.length_drop]
    omega
  have hlast : (l.drop (1 + k))[0] = l[0] := by
    have hright : l[1 + k]? = some l[0] := by
      simpa [List.getElem?_drop, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hi.2.1
    have hleft : (l.drop (1 + k))[0]? = l[1 + k]? := by
      simp [List.getElem?_drop]
    rw [List.getElem?_eq_getElem hlen',
      hright] at hleft
    exact Option.some.inj hleft
  have hunique : lastIndex? (l.drop (1 + k))[0]
      ((l.drop (1 + k)).drop 1) = none := by
    rw [hlast]
    apply lastIndex?_none_iff.mpr
    simpa only [List.drop_drop, ← Nat.add_assoc] using hi.2.2
  have hnonempty : l.drop (1 + k) ≠ [] := by
    apply List.ne_nil_of_length_pos
    simp [List.length_drop]
    omega
  have htail := (scanNonpal_none_drop l (1 + k + 1)).mp hrec
  have hhead := (scanNonpal_none_unique_head (by
    apply List.length_pos_iff_ne_nil.mpr
    exact hnonempty) hunique).mpr
  apply hhead
  simpa [List.drop_drop, Nat.add_assoc] using htail

def contractInitial (w : G.Walk s t) (q : ℕ)
    (hclosed : w.getVert 0 = w.getVert q) : G.Walk s t :=
  (w.drop q).copy (by simpa using hclosed.symm) rfl

theorem contractInitial_support (w : G.Walk s t) (q : ℕ)
    (hq : q ≤ w.length) (hclosed : w.getVert 0 = w.getVert q) :
    (contractInitial w q hclosed).support = w.support.drop q := by
  simp [contractInitial, Walk.drop_support_eq_support_drop_min,
    Nat.min_eq_left hq]

theorem contractInitial_length (w : G.Walk s t) (q : ℕ)
    (hclosed : w.getVert 0 = w.getVert q) :
    (contractInitial w q hclosed).length = w.length - q := by
  simp [contractInitial, Walk.drop_length]

theorem contractInitial_edges (w : G.Walk s t) (q : ℕ)
    (hclosed : w.getVert 0 = w.getVert q) :
    (contractInitial w q hclosed).edges = w.edges.drop q := by
  simp [contractInitial, Walk.edges_drop]

theorem contractInitial_count_le_one (w : G.Walk s t) (q : ℕ)
    (hq : q ≤ w.length) (hclosed : w.getVert 0 = w.getVert q)
    (hpal : (intervalSegment w.support 0 q).reverse =
      intervalSegment w.support 0 q)
    (e : Sym2 V) (hcount : w.edges.count e ≤ 1) :
    (contractInitial w q hclosed).edges.count e = w.edges.count e := by
  let loop : G.Walk s s := (w.take q).copy rfl (by simpa using hclosed.symm)
  have hloop_support : loop.support = intervalSegment w.support 0 q := by
    simp [loop, Walk.support_copy, Walk.support_take, intervalSegment]
  have heven := palindrome_closed_segment_special_count_even
    (G := G) loop (by simpa [hloop_support] using hpal) e
  have hsplit : loop.edges.count e +
      (contractInitial w q hclosed).edges.count e = w.edges.count e := by
    simp only [loop, Walk.edges_copy, Walk.edges_take,
      contractInitial_edges, ← List.count_append,
      List.take_append_drop]
  rcases heven with ⟨k, hk⟩
  omega

theorem contractInitial_special_count (w : G.Walk s t) (q : ℕ)
    (hq : q ≤ w.length) (hclosed : w.getVert 0 = w.getVert q)
    (hpal : (intervalSegment w.support 0 q).reverse =
      intervalSegment w.support 0 q)
    (e : Sym2 V) (hcount : w.edges.count e = 1) :
    (contractInitial w q hclosed).edges.count e = 1 := by
  rw [contractInitial_count_le_one w q hq hclosed hpal e (by omega)]
  exact hcount

/-- If the scan finds no non-palindromic closed interval, erasing its
palindromic intervals leaves a simple path. Each edge used at most once keeps
its multiplicity, and the resulting support is a sublist of the original. -/
theorem path_of_scanNonpal_none (w : G.Walk s t)
    (hscan : scanNonpal w.support 0 = none) :
    ∃ p : G.Walk s t, p.IsPath ∧ p.support.Sublist w.support ∧
      ∀ e : Sym2 V, w.edges.count e ≤ 1 →
        p.edges.count e = w.edges.count e := by
  induction hn : w.length using Nat.strong_induction_on generalizing s w with
  | h n ih =>
      cases w with
      | nil =>
          exact ⟨Walk.nil, by simp, List.Sublist.refl _, by simp⟩
      | cons hadj tail =>
          let w : G.Walk s t := Walk.cons hadj tail
          have hlen : 0 < w.support.length := by simp [w]
          cases hidx : lastIndex? s tail.support with
          | none =>
              have hidx' : lastIndex? w.support[0] (w.support.drop 1) =
                  none := by simpa [w, Walk.support_cons] using hidx
              have htail : scanNonpal tail.support 0 = none := by
                have hs := (scanNonpal_none_unique_head hlen hidx').mp
                  (by simpa only [w] using hscan)
                simpa [w, Walk.support_cons] using hs
              obtain ⟨p, hpath, hsub, hcount⟩ :=
                ih tail.length (by simp [w] at hn; omega) tail htail rfl
              refine ⟨Walk.cons hadj p, ?_, ?_, ?_⟩
              · apply (Walk.cons_isPath_iff hadj p).mpr
                refine ⟨hpath, ?_⟩
                intro hmem
                have hmem' : s ∈ tail.support := hsub.subset hmem
                have hunique := lastIndex?_none_iff.mp hidx
                exact hunique hmem'
              · simpa only [w, Walk.support_cons] using hsub.cons_cons s
              · intro e he
                have htail_le : tail.edges.count e ≤ 1 := by
                  have hbound : tail.edges.count e ≤
                      (Walk.cons hadj tail).edges.count e := by
                    simp only [Walk.edges_cons, List.count_cons]
                    omega
                  exact hbound.trans (by simpa only [w] using he)
                simpa [w, Walk.edges_cons, List.count_cons,
                  hcount e htail_le]
          | some k =>
              have hidx' : lastIndex? w.support[0] (w.support.drop 1) =
                  some k := by simpa [w, Walk.support_cons] using hidx
              have ho := lastIndex?_some_iff.mp hidx'
              have hq : 1 + k ≤ w.length := by
                simp only [List.length_drop] at ho
                have hs := w.length_support
                omega
              have hclosed : w.getVert 0 = w.getVert (1 + k) := by
                have hopt : w.support[0]? = w.support[1 + k]? := by
                  have hright : w.support[1 + k]? = some w.support[0] := by
                    simpa [List.getElem?_drop, Nat.add_assoc, Nat.add_comm,
                      Nat.add_left_comm] using ho.2.1
                  have hleft : w.support[0]? = some w.support[0] := by
                    rw [List.getElem?_eq_getElem (by
                      rw [Walk.length_support]
                      omega)]
                  exact hleft.trans hright.symm
                have hzero := w.getVert_eq_support_getElem? (by omega :
                  0 ≤ w.length)
                have hlast := w.getVert_eq_support_getElem? hq
                rw [← hzero, ← hlast] at hopt
                exact Option.some.inj hopt
              have hpal : (intervalSegment w.support 0 (1 + k)).reverse =
                  intervalSegment w.support 0 (1 + k) := by
                by_contra hnot
                change scanNonpal w.support 0 = none at hscan
                rw [scanNonpal.eq_1] at hscan
                simp only [hlen, ↓reduceDIte, Nat.zero_add, List.drop_zero,
                  hidx'] at hscan
                have hnot' :
                    (List.take (1 + k - 0 + 1) (List.drop 0 w.support)).reverse ≠
                      List.take (1 + k - 0 + 1) (List.drop 0 w.support) := by
                  simpa only [intervalSegment] using hnot
                simp only [List.drop_zero] at hnot'
                rw [if_neg hnot'] at hscan
                contradiction
              have hscan' : scanNonpal (contractInitial w (1 + k) hclosed).support
                  0 = none := by
                rw [contractInitial_support w (1 + k) hq hclosed]
                exact scanNonpal_none_contract hlen (by
                  rw [Walk.length_support]
                  omega) hidx' hpal (by simpa only [w] using hscan)
              have hlt : (contractInitial w (1 + k) hclosed).length < n := by
                rw [contractInitial_length]
                have hwlen : w.length = n := hn
                omega
              obtain ⟨p, hpath, hsub, hcount⟩ :=
                ih _ hlt (contractInitial w (1 + k) hclosed) hscan' rfl
              refine ⟨p, hpath, ?_, ?_⟩
              · exact hsub.trans (by
                  rw [contractInitial_support w (1 + k) hq hclosed]
                  exact List.drop_sublist _ _)
              · intro e he
                rw [hcount e (by
                  rw [contractInitial_count_le_one w (1 + k) hq hclosed hpal e he]
                  exact he),
                  contractInitial_count_le_one w (1 + k) hq hclosed hpal e he]

theorem shorter_target_path_of_scanNonpal_none (w : G.Walk s t)
    (hscan : scanNonpal w.support 0 = none) (hnot : ¬w.IsPath)
    (a b : Sym2 V) (ha : w.edges.count a = 1)
    (hb : w.edges.count b = 1) :
    ∃ p : G.Walk s t,
      p.IsPath ∧ p.edges.count a = 1 ∧ p.edges.count b = 1 ∧
        p.length < w.length := by
  obtain ⟨p, hpath, hsub, hcount⟩ := path_of_scanNonpal_none w hscan
  have hle : p.length ≤ w.length := by
    have hs := hsub.length_le
    simp only [Walk.length_support] at hs
    omega
  have hlt : p.length < w.length := by
    by_contra h
    have heq : p.support = w.support :=
      hsub.eq_of_length (by
        simp only [Walk.length_support]
        omega)
    apply hnot
    apply Walk.IsPath.mk'
    rw [← heq]
    exact hpath.support_nodup
  exact ⟨p, hpath, (hcount a (by omega)).trans ha,
    (hcount b (by omega)).trans hb, hlt⟩

end TwoDoorsProof
