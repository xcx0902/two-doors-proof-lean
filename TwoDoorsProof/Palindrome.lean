import TwoDoorsProof.WalkSum

namespace TwoDoorsProof

section LastIndex

variable {α : Type*} [DecidableEq α]

/-! `lastIndex?` returns the position of the last occurrence of an element. -/

def lastIndex? (a : α) : List α → Option ℕ
  | [] => none
  | x :: xs =>
      match lastIndex? a xs with
      | some n => some (n + 1)
      | none => if a = x then some 0 else none

private theorem lastIndex?_mem {a : α} :
    ∀ {l : List α} {n : ℕ}, lastIndex? a l = some n → a ∈ l
  | [], n, h => by simp [lastIndex?] at h
  | x :: xs, n, h => by
      simp only [lastIndex?] at h
      cases hr : lastIndex? a xs with
      | some k =>
          simp only [hr, Option.some.injEq] at h
          exact List.mem_cons_of_mem x (lastIndex?_mem hr)
      | none =>
          simp only [hr] at h
          by_cases hax : a = x
          · simp [hax] at h
            exact by simp [hax]
          · simp [hax] at h

private theorem lastIndex?_none_iff {a : α} :
    ∀ {l : List α}, lastIndex? a l = none ↔ a ∉ l
  | [] => by simp [lastIndex?]
  | x :: xs => by
      simp only [lastIndex?]
      cases hr : lastIndex? a xs with
      | some k =>
          have hmem : a ∈ xs := lastIndex?_mem hr
          simp [hr, hmem]
      | none =>
          simp only [hr]
          by_cases hax : a = x
          · subst x
            simp
          · simp [hax, (lastIndex?_none_iff (a := a) (l := xs)).mp hr]

private theorem exists_split_mem {a : α} :
    ∀ {l : List α}, a ∈ l ↔ ∃ pre suf, l = pre ++ [a] ++ suf
  | [] => by simp
  | x :: xs => by
      constructor
      · intro h
        rcases (List.mem_cons.mp h) with rfl | h
        · exact ⟨[], xs, by simp⟩
        · rcases (exists_split_mem.mp h) with ⟨pre, suf, hs⟩
          exact ⟨x :: pre, suf, by simp [hs]⟩
      · rintro ⟨pre, suf, h⟩
        simpa [h]

private theorem lastIndex?_spec {a : α} :
    ∀ {l : List α} {n : ℕ},
      lastIndex? a l = some n ↔
        ∃ pre suf, l = pre ++ [a] ++ suf ∧ a ∉ suf ∧ n = pre.length
  | [], n => by simp [lastIndex?]
  | x :: xs, n => by
      simp only [lastIndex?]
      cases hr : lastIndex? a xs with
      | some k =>
          have hxs := (lastIndex?_spec (a := a) (l := xs) (n := k))
          constructor
          · intro h
            simp only [hr, Option.some.injEq] at h
            rcases hxs.mp hr with ⟨pre, suf, hs, hnot, hk⟩
            refine ⟨x :: pre, suf, ?_, hnot, ?_⟩
            · simp [hs]
            · have hk' : k = pre.length := hk
              simpa [List.length_cons, hk'] using h.symm
          · rintro ⟨pre, suf, hs, hnot, hn⟩
            cases pre with
            | nil =>
                have hmem : a ∈ xs := lastIndex?_mem hr
                cases hs
                exact False.elim ((lastIndex?_none_iff.mp
                  (lastIndex?_none_iff.mpr hnot)) hmem)
            | cons y pre =>
                have hxseq : xs = pre ++ [a] ++ suf := by
                  simpa using congrArg List.tail hs
                have hrec : lastIndex? a xs = some pre.length :=
                  (lastIndex?_spec (a := a) (l := xs) (n := pre.length)).mpr
                    ⟨pre, suf, hxseq, hnot, rfl⟩
                have hk : k = pre.length := by
                  rw [hrec] at hr
                  exact (Option.some.inj hr).symm
                simp [hr, hk, hn, List.length_cons]
      | none =>
          have hnone : a ∉ xs := lastIndex?_none_iff.mp hr
          constructor
          · intro h
            simp only [hr] at h
            by_cases hax : a = x
            · subst x
              simp only [↓reduceIte, Option.some.injEq] at h
              refine ⟨[], xs, by simp, hnone, by simpa using h.symm⟩
            · simp [hax] at h
          · rintro ⟨pre, suf, hs, hnot, hn⟩
            cases pre with
            | nil =>
                have hxseq : xs = suf := by
                  simpa using congrArg List.tail hs
                have hxa : x = a := by
                  simpa using congrArg List.head? hs
                subst x
                have hnone : lastIndex? a xs = none := by
                  rw [hxseq]
                  exact lastIndex?_none_iff.mpr hnot
                simp [lastIndex?, hnone, hn]
            | cons y pre =>
                have hxseq : xs = pre ++ [a] ++ suf := by
                  simpa using congrArg List.tail hs
                have hrec : lastIndex? a xs = some pre.length :=
                  (lastIndex?_spec (a := a) (l := xs) (n := pre.length)).mpr
                    ⟨pre, suf, hxseq, hnot, rfl⟩
                rw [hrec] at hr
                contradiction

private theorem lastIndex?_getElem {a : α} :
    ∀ {l : List α} {n : ℕ}, lastIndex? a l = some n →
      n < l.length ∧ l[n]? = some a
  | [], n, h => by simp [lastIndex?] at h
  | x :: xs, n, h => by
      simp only [lastIndex?] at h
      cases hr : lastIndex? a xs with
      | some k =>
          simp only [hr, Option.some.injEq] at h
          subst n
          have hrec := lastIndex?_getElem (a := a) (l := xs) (n := k) hr
          refine ⟨by simp [hrec.1], ?_⟩
          have hval : xs[k]'hrec.1 = a := by
            rw [← Option.some_inj, ← List.getElem?_eq_getElem hrec.1]
            exact hrec.2
          have hkcons : k + 1 < (x :: xs).length := by
            simp [hrec.1]
          rw [List.getElem?_eq_getElem hkcons]
          simpa using hval
      | none =>
          simp only [hr] at h
          by_cases hax : a = x
          · subst x
            simp only [↓reduceIte, Option.some.injEq] at h
            subst n
            simp
          · simp [hax] at h

/-! Scan from left to right. A palindromic first-to-last loop is skipped, while
the first non-palindromic such loop is returned. The recursion measure is the
number of original list entries at or after the current position. -/

def scanNonpal (l : List α) : (p : ℕ) → Option (ℕ × ℕ)
  | p =>
      if hp : p < l.length then
        let x := l[p]
        match lastIndex? x (l.drop (p + 1)) with
        | none => scanNonpal l (p + 1)
        | some k =>
            let q := p + 1 + k
            let segment := (l.drop p).take (q - p + 1)
            if segment.reverse = segment then
              scanNonpal l (q + 1)
            else
              some (p, q)
      else
        none
termination_by p => l.length - p
decreasing_by
  all_goals
    simp_wf
    omega

def intervalSegment (l : List α) (p q : ℕ) : List α :=
  (l.drop p).take (q - p + 1)

def reverseInterval (l : List α) (p q : ℕ) : List α :=
  l.take p ++ (intervalSegment l p q).reverse ++ l.drop (q + 1)

private theorem intervalSegment_length
    {l : List α} {p q : ℕ} (hpq : p ≤ q) (hq : q < l.length) :
    (intervalSegment l p q).length = q - p + 1 := by
  unfold intervalSegment
  rw [List.length_take]
  have hdrop : q - p + 1 ≤ (l.drop p).length := by
    rw [List.length_drop]
    omega
  rw [Nat.min_eq_left hdrop]

private theorem reverseInterval_prefix
    {l : List α} {p q : ℕ} (hp : p ≤ l.length) :
    (reverseInterval l p q).take p = l.take p := by
  unfold reverseInterval
  rw [List.take_append, List.take_append]
  simp [List.take_take, hp]

private theorem reverseInterval_middle
    {l : List α} {p q : ℕ} (hpq : p ≤ q) (hq : q < l.length) :
    ((reverseInterval l p q).drop p).take (q - p + 1) =
      (intervalSegment l p q).reverse := by
  unfold reverseInterval
  have hseg := intervalSegment_length (l := l) hpq hq
  have hp : p ≤ l.length := by omega
  rw [List.drop_append, List.drop_append]
  have hmin : min p l.length = p := Nat.min_eq_left hp
  simp [hmin, hseg]

private theorem reverseInterval_suffix
    {l : List α} {p q : ℕ} (hpq : p ≤ q) (hq : q < l.length) :
    (reverseInterval l p q).drop (q + 1) = l.drop (q + 1) := by
  unfold reverseInterval
  have htake : (l.take p).length = p := by
    rw [List.length_take, Nat.min_eq_left (by omega)]
  have hwhole :
      (l.take p ++ (intervalSegment l p q).reverse).length = q + 1 := by
    rw [List.length_append, htake, List.length_reverse,
      intervalSegment_length hpq hq]
    omega
  change
    List.drop (q + 1)
        ((l.take p ++ (intervalSegment l p q).reverse) ++ l.drop (q + 1)) =
      l.drop (q + 1)
  rw [List.drop_append_of_le_length (by simpa [hwhole])]
  have hdrop :
      List.drop (q + 1) (l.take p ++ (intervalSegment l p q).reverse) = [] := by
    apply List.drop_eq_nil_of_le
    rw [hwhole]
  rw [hdrop]
  simp

private theorem interval_decomposition
    {l : List α} {p q : ℕ} (hpq : p ≤ q) (hq : q < l.length) :
    l.take p ++ intervalSegment l p q ++ l.drop (q + 1) = l := by
  unfold intervalSegment
  have hdrop : (l.drop p).drop (q - p + 1) = l.drop (q + 1) := by
    rw [List.drop_drop]
    congr 1
    omega
  rw [← hdrop, List.append_assoc, List.take_append_drop, List.take_append_drop]

theorem reverseInterval_length
    {l : List α} {p q : ℕ} (hpq : p ≤ q) (hq : q < l.length) :
    (reverseInterval l p q).length = l.length := by
  unfold reverseInterval
  have hdecomp := interval_decomposition (l := l) hpq hq
  have hlen := congrArg List.length hdecomp
  simpa [List.length_append] using hlen

theorem reverseInterval_involutive
    {l : List α} {p q : ℕ} (hpq : p ≤ q) (hq : q < l.length) :
    reverseInterval (reverseInterval l p q) p q = l := by
  have hlen := reverseInterval_length (l := l) hpq hq
  have hq' : q < (reverseInterval l p q).length := by omega
  change (reverseInterval l p q).take p ++
      (intervalSegment (reverseInterval l p q) p q).reverse ++
      (reverseInterval l p q).drop (q + 1) = l
  rw [reverseInterval_prefix (by omega)]
  change l.take p ++
      (((reverseInterval l p q).drop p).take (q - p + 1)).reverse ++
      (reverseInterval l p q).drop (q + 1) = l
  rw [reverseInterval_middle hpq hq, List.reverse_reverse,
    reverseInterval_suffix hpq hq]
  exact interval_decomposition hpq hq

theorem reverseInterval_perm
    {l : List α} {p q : ℕ} (hpq : p ≤ q) (hq : q < l.length) :
    List.Perm (reverseInterval l p q) l := by
  have hperm :
      List.Perm
        (l.take p ++ (intervalSegment l p q).reverse ++ l.drop (q + 1))
        (l.take p ++ intervalSegment l p q ++ l.drop (q + 1)) := by
    simpa only [List.append_assoc] using
      ((List.reverse_perm (intervalSegment l p q)).append_right
        (l.drop (q + 1))).append_left (l.take p)
  simpa only [reverseInterval, interval_decomposition hpq hq] using hperm

theorem reverseInterval_drop_perm
    {l : List α} {p q n : ℕ} (hpq : p ≤ q) (hq : q < l.length)
    (hn : n ≤ p) :
    List.Perm ((reverseInterval l p q).drop n) (l.drop n) := by
  apply (reverseInterval_perm hpq hq).drop_of_getElem?
  intro j hj
  have hp : p ≤ l.length := by omega
  have hprefix := reverseInterval_prefix (l := l) (p := p) (q := q) hp
  have hopt := congrArg (fun xs : List α => xs[j]?) hprefix
  simpa [List.getElem?_take, hj, Nat.lt_of_lt_of_le hj hn] using hopt

private theorem intervalSegment_eq_of_lastIndex
    {l : List α} {p k : ℕ} (hp : p < l.length)
  (hidx : lastIndex? l[p] (l.drop (p + 1)) = some k) :
    intervalSegment l p (p + 1 + k) =
      l[p] :: (l.drop (p + 1)).take (k + 1) := by
  have hpos : 0 < (p + 1 + k) - p + 1 := by omega
  rw [intervalSegment, List.drop_eq_getElem_cons hp, List.take_cons hpos]
  have harg : (p + 1 + k) - p + 1 = k + 2 := by omega
  rw [harg]
  simp

private theorem getLast?_take_succ {l : List α} {k : ℕ} (hk : k < l.length) :
    (l.take (k + 1)).getLast? = l[k]? := by
  rw [List.getLast?_eq_getElem?]
  rw [List.length_take, Nat.min_eq_left (by omega)]
  simp

private theorem intervalSegment_last_eq_of_lastIndex
    {l : List α} {p k : ℕ} (hp : p < l.length)
    (hidx : lastIndex? l[p] (l.drop (p + 1)) = some k) :
    (intervalSegment l p (p + 1 + k)).getLast? = some l[p] := by
  have hget := lastIndex?_getElem
    (a := l[p]) (l := l.drop (p + 1)) (n := k) hidx
  have htail :
      (l.drop (p + 1)).take (k + 1) ≠ [] := by
    apply List.ne_nil_of_length_pos
    rw [List.length_take, Nat.min_eq_left (by omega)]
    omega
  have hseg :
      intervalSegment l p (p + 1 + k) =
        l[p] :: (l.drop (p + 1)).take (k + 1) :=
    intervalSegment_eq_of_lastIndex hp hidx
  rw [hseg]
  simp only [List.getLast?_cons]
  rw [getLast?_take_succ hget.1]
  rw [hget.2]
  rfl

theorem scanNonpal_result
    {l : List α} {p r q : ℕ} (hscan : scanNonpal l p = some (r, q)) :
    p ≤ r ∧ r < q ∧ (intervalSegment l r q).reverse ≠ intervalSegment l r q := by
  induction hmeasure : l.length - p using Nat.strong_induction_on generalizing p with
  | h m ih =>
      by_cases hp : p < l.length
      · rw [scanNonpal.eq_1] at hscan
        simp only [hp, ↓reduceDIte] at hscan
        cases hidx : lastIndex? l[p] (l.drop (p + 1)) with
        | none =>
            simp only [hidx] at hscan
            have hlt : l.length - (p + 1) < m := by omega
            have hrec := ih (l.length - (p + 1)) hlt hscan rfl
            exact ⟨by omega, hrec.2.1, hrec.2.2⟩
        | some k =>
            simp only [hidx] at hscan
            let q₀ := p + 1 + k
            let seg := intervalSegment l p q₀
            by_cases hpal : seg.reverse = seg
            · have hlt : l.length - (q₀ + 1) < m := by
                dsimp [q₀]
                omega
              have hpal' :
                  (List.take (p + 1 + k - p + 1) (List.drop p l)).reverse =
                    List.take (p + 1 + k - p + 1) (List.drop p l) := by
                simpa [intervalSegment, q₀, seg] using hpal
              rw [if_pos hpal'] at hscan
              have hscan' : scanNonpal l (q₀ + 1) = some (r, q) := by
                simpa [q₀] using hscan
              have hrec := ih (l.length - (q₀ + 1)) hlt hscan' rfl
              exact ⟨by omega, hrec.2.1, hrec.2.2⟩
            · have hdirect : some (p, q₀) = some (r, q) := by
                have hpal' :
                    (List.take (p + 1 + k - p + 1) (List.drop p l)).reverse ≠
                      List.take (p + 1 + k - p + 1) (List.drop p l) := by
                  simpa [intervalSegment, q₀, seg] using hpal
                rw [if_neg hpal'] at hscan
                simpa [q₀] using hscan
              have hpq := Option.some.inj hdirect
              have hpr : p = r := congrArg Prod.fst hpq
              have hq : q₀ = q := congrArg Prod.snd hpq
              subst r
              subst q
              exact ⟨le_rfl, by dsimp [q₀]; omega, hpal⟩
      · rw [scanNonpal.eq_1] at hscan
        exact False.elim (by simpa [hp] using hscan)

theorem scanNonpal_result_endpoint
    {l : List α} {p r q : ℕ} (hscan : scanNonpal l p = some (r, q)) :
    p ≤ r ∧ r < q ∧ q < l.length ∧ l[r]? = l[q]? := by
  induction hmeasure : l.length - p using Nat.strong_induction_on generalizing p with
  | h m ih =>
      by_cases hp : p < l.length
      · rw [scanNonpal.eq_1] at hscan
        simp only [hp, ↓reduceDIte] at hscan
        cases hidx : lastIndex? l[p] (l.drop (p + 1)) with
        | none =>
            simp only [hidx] at hscan
            have hlt : l.length - (p + 1) < m := by omega
            have hrec := ih (l.length - (p + 1)) hlt hscan rfl
            exact ⟨by omega, hrec.2.1, hrec.2.2.1, hrec.2.2.2⟩
        | some k =>
            simp only [hidx] at hscan
            let q₀ := p + 1 + k
            let seg := intervalSegment l p q₀
            by_cases hpal : seg.reverse = seg
            · have hlt : l.length - (q₀ + 1) < m := by
                dsimp [q₀]
                omega
              have hpal' :
                  (List.take (p + 1 + k - p + 1) (List.drop p l)).reverse =
                    List.take (p + 1 + k - p + 1) (List.drop p l) := by
                simpa [intervalSegment, q₀, seg] using hpal
              rw [if_pos hpal'] at hscan
              have hscan' : scanNonpal l (q₀ + 1) = some (r, q) := by
                simpa [q₀] using hscan
              have hrec := ih (l.length - (q₀ + 1)) hlt hscan' rfl
              exact ⟨by omega, hrec.2.1, hrec.2.2.1, hrec.2.2.2⟩
            · have hdirect : some (p, q₀) = some (r, q) := by
                have hpal' :
                    (List.take (p + 1 + k - p + 1) (List.drop p l)).reverse ≠
                      List.take (p + 1 + k - p + 1) (List.drop p l) := by
                  simpa [intervalSegment, q₀, seg] using hpal
                rw [if_neg hpal'] at hscan
                simpa [q₀] using hscan
              have hpq := Option.some.inj hdirect
              have hpr : p = r := congrArg Prod.fst hpq
              have hq : q₀ = q := congrArg Prod.snd hpq
              have hget := lastIndex?_getElem
                (a := l[p]) (l := l.drop (p + 1)) (n := k) hidx
              have hq0 : q₀ < l.length := by
                dsimp [q₀]
                rw [List.length_drop] at hget
                omega
              have hqopt : l[q₀]? = some l[p] := by
                change l[p + 1 + k]? = some l[p]
                rw [← List.getElem?_drop]
                simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hget.2
              have hpopt : l[p]? = some l[p] := by
                rw [List.getElem?_eq_getElem hp]
              subst r
              subst q
              exact ⟨le_rfl, by dsimp [q₀]; omega, hq0, hpopt.trans hqopt.symm⟩
      · rw [scanNonpal.eq_1] at hscan
        exact False.elim (by simpa [hp] using hscan)

end LastIndex

section WalkIntervals

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {s t : V}

/-- The subwalk between two positions, with its endpoint identified by `getVert`. -/
def intervalWalk (w : G.Walk s t) (p q : ℕ) (hpq : p ≤ q) :
    G.Walk (w.getVert p) (w.getVert q) :=
  ((w.drop p).take (q - p)).copy rfl (by
    rw [Walk.drop_getVert]
    congr 1
    omega)

/-- Reverse a closed interval while retaining its original prefix and suffix. -/
def flipWalkAt (w : G.Walk s t) (p q : ℕ) (hpq : p ≤ q)
    (hclosed : w.getVert p = w.getVert q) : G.Walk s t :=
  flipClosed (w.take p)
    ((intervalWalk w p q hpq).copy rfl hclosed.symm)
    ((w.drop q).copy hclosed.symm rfl)

theorem intervalWalk_support (w : G.Walk s t) (p q : ℕ)
    (hpq : p ≤ q) (hq : q ≤ w.length) :
    (intervalWalk w p q hpq).support = intervalSegment w.support p q := by
  simp only [intervalWalk, Walk.support_copy, Walk.support_take,
    Walk.drop_support_eq_support_drop_min]
  rw [Nat.min_eq_left (by omega)]
  change (w.support.drop p).take (q - p + 1) =
    intervalSegment w.support p q
  rfl

theorem intervalWalk_length (w : G.Walk s t) (p q : ℕ)
    (hpq : p ≤ q) (hq : q ≤ w.length) :
    (intervalWalk w p q hpq).length = q - p := by
  simp [intervalWalk, Nat.min_eq_left (by omega), Walk.drop_length]
  omega

theorem flipWalkAt_length (w : G.Walk s t) (p q : ℕ)
    (hpq : p ≤ q) (hq : q ≤ w.length)
    (hclosed : w.getVert p = w.getVert q) :
    (flipWalkAt w p q hpq hclosed).length = w.length := by
  unfold flipWalkAt flipClosed
  simp [intervalWalk_length w p q hpq hq,
    Nat.min_eq_left (by omega)]
  omega

theorem flipWalkAt_support (w : G.Walk s t) (p q : ℕ)
    (hpq : p ≤ q) (hq : q ≤ w.length)
    (hclosed : w.getVert p = w.getVert q) :
    (flipWalkAt w p q hpq hclosed).support =
      reverseInterval w.support p q := by
  have hp : p < w.support.length := by
    rw [Walk.length_support]
    omega
  have hloop :
      w.support[p] :: (intervalSegment w.support p q).reverse.tail =
        (intervalSegment w.support p q).reverse := by
    have hc := (((intervalWalk w p q hpq).copy rfl hclosed.symm).reverse).cons_tail_support
    rw [Walk.support_reverse, Walk.support_copy,
      intervalWalk_support w p q hpq hq] at hc
    have hget : w.getVert p = w.support[p] :=
      w.getVert_eq_support_getElem (by omega)
    simpa only [hget, List.tail_reverse] using hc
  have hsuffix :
      ((w.drop q).copy hclosed.symm rfl).support.tail =
        w.support.drop (q + 1) := by
    rw [Walk.support_copy, Walk.drop_support_eq_support_drop_min,
      Nat.min_eq_left hq, List.tail_drop]
  simp only [flipWalkAt, flipClosed, Walk.support_append,
    Walk.support_take, Walk.support_reverse, Walk.support_copy,
    intervalWalk_support w p q hpq hq, hsuffix]
  rw [List.take_succ_eq_append_getElem hp]
  simp only [List.append_assoc, List.singleton_append]
  rw [hloop]
  rw [Walk.drop_support_eq_support_drop_min, Nat.min_eq_left hq, List.tail_drop]
  simp only [reverseInterval, List.append_assoc]

theorem flipWalkAt_closed (w : G.Walk s t) (p q : ℕ)
    (hpq : p < q) (hq : q ≤ w.length)
    (hclosed : w.getVert p = w.getVert q) :
    (flipWalkAt w p q hpq.le hclosed).getVert p =
      (flipWalkAt w p q hpq.le hclosed).getVert q := by
  let pre := w.take p
  let loop : G.Walk (w.getVert p) (w.getVert p) :=
    (intervalWalk w p q hpq.le).copy rfl hclosed.symm
  let suffix : G.Walk (w.getVert p) t :=
    (w.drop q).copy hclosed.symm rfl
  have hpre : pre.length = p := by
    dsimp [pre]
    rw [Walk.take_length, Nat.min_eq_left (by omega)]
  have hloop : loop.length = q - p := by
    dsimp [loop]
    rw [Walk.length_copy, intervalWalk_length w p q hpq.le hq]
  have hsum : (pre.append loop.reverse).length = q := by
    simp [hpre, hloop]
    omega
  have hleft :
      (flipWalkAt w p q hpq.le hclosed).getVert p = w.getVert p := by
    change ((pre.append loop.reverse).append suffix).getVert p = w.getVert p
    rw [Walk.getVert_append']
    simp [Walk.getVert_append', hpre, hsum, pre] <;> omega
  have hright :
      (flipWalkAt w p q hpq.le hclosed).getVert q = w.getVert p := by
    change ((pre.append loop.reverse).append suffix).getVert q = w.getVert p
    rw [Walk.getVert_append']
    simp [Walk.getVert_append', hpre, hsum, hloop,
      Walk.getVert_reverse, hpq.not_ge]
  exact hleft.trans hright.symm

theorem reverseInterval_ne_of_nonpalindrome [DecidableEq V]
    {l : List V} {p q : ℕ}
    (hpq : p ≤ q) (hq : q < l.length)
    (hnot : (intervalSegment l p q).reverse ≠ intervalSegment l p q) :
    reverseInterval l p q ≠ l := by
  intro heq
  apply hnot
  have hmiddle := reverseInterval_middle (l := l) hpq hq
  rw [heq] at hmiddle
  exact hmiddle.symm

theorem flipWalkAt_ne_of_nonpalindrome [DecidableEq V]
    (w : G.Walk s t) (p q : ℕ) (hpq : p ≤ q) (hq : q ≤ w.length)
    (hclosed : w.getVert p = w.getVert q)
    (hnot : (intervalSegment w.support p q).reverse ≠
      intervalSegment w.support p q) :
    flipWalkAt w p q hpq hclosed ≠ w := by
  intro heq
  have hs := congrArg Walk.support heq
  rw [flipWalkAt_support w p q hpq hq hclosed] at hs
  exact reverseInterval_ne_of_nonpalindrome hpq (by
    rw [Walk.length_support]
    omega) hnot hs

theorem flipWalkAt_twice [DecidableEq V] (w : G.Walk s t) (p q : ℕ)
    (hpq : p < q) (hq : q ≤ w.length)
    (hclosed : w.getVert p = w.getVert q) :
    flipWalkAt (flipWalkAt w p q hpq.le hclosed) p q hpq.le
        (flipWalkAt_closed w p q hpq hq hclosed) = w := by
  have hq' : q ≤ (flipWalkAt w p q hpq.le hclosed).length := by
    rw [flipWalkAt_length w p q hpq.le hq hclosed]
    exact hq
  apply Walk.ext_support
  rw [flipWalkAt_support _ p q hpq.le hq'
      (flipWalkAt_closed w p q hpq hq hclosed),
    flipWalkAt_support w p q hpq.le hq hclosed,
    reverseInterval_involutive hpq.le (by
      rw [Walk.length_support]
      omega)]

theorem flipWalkAt_count (w : G.Walk s t) (p q : ℕ)
    [DecidableEq V]
    (hpq : p ≤ q) (hq : q ≤ w.length)
    (hclosed : w.getVert p = w.getVert q) (e : Sym2 V) :
    (flipWalkAt w p q hpq hclosed).edges.count e = w.edges.count e := by
  unfold flipWalkAt flipClosed intervalWalk
  simp only [Walk.edges_append, Walk.edges_reverse, List.count_append,
    List.count_reverse, Walk.edges_copy, Walk.edges_take, Walk.edges_drop]
  have hsplit : w.edges.take p ++ (w.edges.drop p).take (q - p) ++
      w.edges.drop q = w.edges := by
    have hd : (w.edges.drop p).drop (q - p) = w.edges.drop q := by
      rw [List.drop_drop]
      congr 1
      omega
    rw [← hd, List.append_assoc, List.take_append_drop, List.take_append_drop]
  simpa [List.count_append, add_assoc] using
    congrArg (fun l : List (Sym2 V) => l.count e) hsplit

theorem flipWalkAt_weight {R : Type*} [CommMonoid R] (z : Sym2 V → R)
    (w : G.Walk s t) (p q : ℕ) (hpq : p ≤ q) (hq : q ≤ w.length)
    (hclosed : w.getVert p = w.getVert q) :
    walkWeight G s t z (flipWalkAt w p q hpq hclosed) =
      walkWeight G s t z w := by
  unfold flipWalkAt flipClosed intervalWalk walkWeight
  simp only [Walk.edges_append, Walk.edges_reverse, Walk.edges_copy,
    Walk.edges_take, Walk.edges_drop, List.map_append, List.prod_append,
    List.map_reverse, List.prod_reverse]
  have hsplit : w.edges.take p ++ (w.edges.drop p).take (q - p) ++
      w.edges.drop q = w.edges := by
    have hd : (w.edges.drop p).drop (q - p) = w.edges.drop q := by
      rw [List.drop_drop]
      congr 1
      omega
    rw [← hd, List.append_assoc, List.take_append_drop, List.take_append_drop]
  simpa [List.map_append, List.prod_append, mul_assoc] using
    congrArg (fun l : List (Sym2 V) => (l.map z).prod) hsplit

end WalkIntervals

end TwoDoorsProof
