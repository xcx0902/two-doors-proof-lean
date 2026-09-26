import TwoDoorsProof.ComplementDenominator
import TwoDoorsProof.DeterminantGenerating

namespace TwoDoorsProof

open Matrix PowerSeries SimpleGraph
open scoped Matrix

noncomputable section

variable {V R : Type*} [DecidableEq V] [Fintype V] [CommRing R]
variable {s t : V}

def pathWalkOfChain
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : DirectedPathList s t) (hchain : p.list.IsChain G.Adj) :
    G.Walk s t := by
  have hs : p.list.head p.nonempty = s :=
    p.first_eq.trans p.first_is_s
  have ht : p.list.getLast p.nonempty = t :=
    p.last_eq.trans p.last_is_t
  exact (SimpleGraph.Walk.ofSupport p.list p.nonempty hchain).copy hs ht

def pathCycleEdges (p : DirectedPathList s t) : List (Sym2 V) :=
  p.list.dropLast.map (fun x => s(x, cycleOfPath p x))

theorem pathCycleEdges_eq_walk_edges
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : DirectedPathList s t) (hchain : p.list.IsChain G.Adj) :
    pathCycleEdges p = (pathWalkOfChain G p hchain).edges := by
  change p.list.dropLast.map
      (fun x => s(x, (cycleOfPath p) x)) =
    (pathWalkOfChain G p hchain).edges
  calc
    p.list.dropLast.map
        (fun x => s(x, (cycleOfPath p) x)) =
        List.zipWith (fun x y => s(x, y)) p.list p.list.tail := by
          simpa only [cycleOfPath] using
            (formPerm_dropLast_map_eq_zipWith p.list p.nonempty p.nodup)
    _ = (pathWalkOfChain G p hchain).edges := by
      rw [SimpleGraph.Walk.edges_eq_zipWith_support]
      simp [pathWalkOfChain, SimpleGraph.Walk.support_ofSupport]

theorem pathCycleEdges_count_eq_walk_count
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : DirectedPathList s t) (hchain : p.list.IsChain G.Adj)
    (e : Sym2 V) :
    (pathCycleEdges p).count e =
      (pathWalkOfChain G p hchain).edges.count e := by
  rw [pathCycleEdges_eq_walk_edges G p hchain]

theorem chain_rel_cycleOfPath
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : DirectedPathList s t) (hchain : p.list.IsChain G.Adj)
    {x : V} (hx : x ∈ p.list.dropLast) :
    G.Adj x (cycleOfPath p x) := by
  obtain ⟨i, hi, hxi⟩ := List.getElem_of_mem hx
  subst x
  have hi_drop : i < p.list.dropLast.length := by
    simpa using hi
  have hi_list : i < p.list.length := by
    simp [List.length_dropLast] at hi_drop
    omega
  have hi' : i + 1 < p.list.length := by
    simp [List.length_dropLast] at hi_drop
    omega
  have hadj := (List.isChain_iff_getElem.mp hchain) i hi'
  have hmem : p.list[i] ∈ p.list := List.getElem_mem hi_list
  have hnext :=
    List.formPerm_apply_mem_eq_next p.nodup p.list[i] hmem
  rw [List.next_getElem p.list p.nodup i hi_list] at hnext
  simp [cycleOfPath, Nat.mod_eq_of_lt hi', hnext] at hadj ⊢
  exact hadj

theorem pathMatrixWeight_weightedAdj_eq_walkWeight
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : DirectedPathList s t) (hchain : p.list.IsChain G.Adj)
    (a b : Sym2 V) (z : Sym2 V → R) :
    pathMatrixWeight (weightedAdj G (markedEdgeWeight a b z)) p =
      walkWeight G s t (markedEdgeWeight a b z)
        (pathWalkOfChain G p hchain) := by
  have hmap :
      p.list.dropLast.map
          (fun x => weightedAdj G (markedEdgeWeight a b z)
            x (cycleOfPath p x)) =
        (pathCycleEdges p).map (markedEdgeWeight a b z) := by
    calc
      p.list.dropLast.map
          (fun x => weightedAdj G (markedEdgeWeight a b z)
            x (cycleOfPath p x)) =
          p.list.dropLast.map
            (fun x => markedEdgeWeight a b z
              s(x, cycleOfPath p x)) := by
        apply List.map_congr_left
        intro x hx
        rw [weightedAdj_apply G (markedEdgeWeight a b z)
          x (cycleOfPath p x) (chain_rel_cycleOfPath G p hchain hx)]
      _ = (pathCycleEdges p).map (markedEdgeWeight a b z) := by
        unfold pathCycleEdges
        rw [List.map_map]
        simp [Function.comp_def]
  calc
    pathMatrixWeight (weightedAdj G (markedEdgeWeight a b z)) p =
        (p.list.dropLast.map
          (fun x => weightedAdj G (markedEdgeWeight a b z)
            x (cycleOfPath p x))).prod :=
      pathMatrixWeight_eq_dropLast_prod _ _
    _ = ((pathCycleEdges p).map (markedEdgeWeight a b z)).prod := by
      rw [hmap]
    _ = ((pathWalkOfChain G p hchain).edges.map
      (markedEdgeWeight a b z)).prod := by
      rw [pathCycleEdges_eq_walk_edges G p hchain]
    _ = walkWeight G s t (markedEdgeWeight a b z)
        (pathWalkOfChain G p hchain) := rfl

theorem markedCoeffSeries_X_pow_C
    (n : ℕ) (w : Marked R) :
    markedCoeffSeries ((X : (Marked R)⟦X⟧) ^ n * C w) =
      X ^ n * C (markedCoeff w) := by
  apply PowerSeries.ext
  intro d
  rw [markedCoeffSeries_coeff, coeff_X_pow_mul']
  by_cases h : n ≤ d
  · rw [if_pos h, PowerSeries.coeff_C]
    by_cases hd : d ≤ n
    · have hEq : d = n := Nat.le_antisymm hd h
      simp [hEq]
    · have hne : d ≠ n := by omega
      have hsub : d - n ≠ 0 := by omega
      rw [if_neg hsub]
      simp [hne, markedCoeff]
  · rw [if_neg h]
    have hne : d ≠ n := by omega
    simp [hne, markedCoeff]

theorem markedCoeffSeries_path_term
    (n : ℕ) (w : Marked R) (q : R⟦X⟧) :
    markedCoeffSeries
        (((X : (Marked R)⟦X⟧) ^ n * C w) *
          PowerSeries.map markConstHom q) =
      (X : R⟦X⟧) ^ n * C (markedCoeff w) * q := by
  rw [mul_comm ((X : (Marked R)⟦X⟧) ^ n * C w)
      (PowerSeries.map markConstHom q),
    markedCoeffSeries_const_mul,
    markedCoeffSeries_X_pow_C]
  ring

def pathComplementDenominator (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : DirectedPathList s t) (a b : Sym2 V)
    (z : Sym2 V → R) : R⟦X⟧ :=
  ((matrixResolvent (weightedAdj G (ordinaryEdgeWeight a b z))).submatrix
    (fun x : {x : V // x ∉ p.list} => (x : V))
    (fun x : {x : V // x ∉ p.list} => (x : V))).det

theorem pathComplementDenominator_constant_one
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : DirectedPathList s t) (a b : Sym2 V)
    (z : Sym2 V → R) :
    coeff 0 (pathComplementDenominator G p a b z) = 1 := by
  unfold pathComplementDenominator
  exact matrixResolvent_submatrix_det_constant_one _
    (fun x : {x : V // x ∉ p.list} => (x : V))
    Subtype.coe_injective

def directedPathListOfWalk
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : G.Walk s t) (hp : p.IsPath) (hpos : 0 < p.length) :
    DirectedPathList s t :=
  { list := p.support
    nonempty := p.support_ne_nil
    nodup := hp.support_nodup
    length := by
      rw [p.length_support]
      omega
    first := s
    last := t
    first_eq := p.head_support
    last_eq := p.getLast_support
    first_is_s := rfl
    last_is_t := rfl }

theorem directedPathListOfWalk_chain
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : G.Walk s t) (hp : p.IsPath) (hpos : 0 < p.length) :
    (directedPathListOfWalk G p hp hpos).list.IsChain G.Adj :=
  p.isChain_adj_support

theorem pathWalkOfChain_support
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : DirectedPathList s t) (hchain : p.list.IsChain G.Adj) :
    (pathWalkOfChain G p hchain).support = p.list := by
  simp [pathWalkOfChain]

theorem pathWalkOfChain_length
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : DirectedPathList s t) (hchain : p.list.IsChain G.Adj) :
    (pathWalkOfChain G p hchain).length = p.list.length - 1 := by
  simp [pathWalkOfChain]

theorem pathWalkOfChain_isPath
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : DirectedPathList s t) (hchain : p.list.IsChain G.Adj) :
    (pathWalkOfChain G p hchain).IsPath := by
  apply SimpleGraph.Walk.IsPath.mk'
  rw [pathWalkOfChain_support G p hchain]
  exact p.nodup

theorem pathWalkOfChain_of_directedPathListOfWalk
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {p : G.Walk s t} (hp : p.IsPath) (hpos : 0 < p.length) :
    pathWalkOfChain G
        (directedPathListOfWalk G p hp hpos)
        (directedPathListOfWalk_chain G p hp hpos) = p := by
  apply SimpleGraph.Walk.ext_support
  unfold pathWalkOfChain directedPathListOfWalk
  change
    ((SimpleGraph.Walk.ofSupport p.support p.support_ne_nil
      p.isChain_adj_support).copy _ _).support = p.support
  rw [SimpleGraph.Walk.ofSupport_support]
  simp only [SimpleGraph.Walk.support_copy]

theorem directedPathListOfWalk_pathWalkOfChain
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : DirectedPathList s t) (hchain : p.list.IsChain G.Adj) :
    directedPathListOfWalk
        G
        (pathWalkOfChain G p hchain)
        (pathWalkOfChain_isPath G p hchain)
        (by
          rw [pathWalkOfChain_length G p hchain]
          have hlen : 2 ≤ p.list.length := p.length
          omega) = p := by
  apply directedPathList_ext
  · change (pathWalkOfChain G p hchain).support = p.list
    rw [pathWalkOfChain_support G p hchain]
  · exact p.first_is_s.symm
  · exact p.last_is_t.symm

theorem pathMatrixWeight_zero_of_not_chain
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : DirectedPathList s t) (a b : Sym2 V)
    (z : Sym2 V → R)
    (hchain : ¬ p.list.IsChain G.Adj) :
    pathMatrixWeight (weightedAdj G (markedEdgeWeight a b z)) p = 0 := by
  rw [pathMatrixWeight_eq_dropLast_prod]
  obtain ⟨i, hi, hbad⟩ :=
    List.exists_not_getElem_of_not_isChain hchain
  have hi_drop : i < p.list.dropLast.length := by
    simp [List.length_dropLast] at hi ⊢
    omega
  have hmem : p.list[i] ∈ p.list.dropLast :=
    by
      have hmem' : p.list.dropLast[i] ∈ p.list.dropLast :=
        List.getElem_mem hi_drop
      simpa only [List.getElem_dropLast hi_drop] using hmem'
  have hnext :
      cycleOfPath p p.list[i] = p.list[i + 1]'(by omega) := by
    have hmem' : p.list[i] ∈ p.list :=
      List.getElem_mem (by omega)
    have hform :=
      List.formPerm_apply_mem_eq_next p.nodup p.list[i] hmem'
    rw [List.next_getElem p.list p.nodup i (by omega)] at hform
    have hlt : i + 1 < p.list.length := by omega
    change p.list.formPerm p.list[i] = p.list[i + 1]
    simpa only [Nat.mod_eq_of_lt hlt] using hform
  apply List.prod_eq_zero
  apply List.mem_map.mpr
  refine ⟨p.list[i], hmem, ?_⟩
  rw [hnext]
  exact weightedAdj_apply_of_not_adj
    G (markedEdgeWeight a b z) p.list[i] p.list[i + 1] hbad

theorem markedCoeffSeries_path_term_of_chain
    (hab : a ≠ b)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : DirectedPathList s t) (hchain : p.list.IsChain G.Adj)
    (ha : (pathCycleEdges p).count a = 1)
    (hb : (pathCycleEdges p).count b = 1)
    (z : Sym2 V → R) :
    markedCoeffSeries
        (((X : (Marked R)⟦X⟧) ^ (p.list.length - 1) *
          C (pathMatrixWeight
            (weightedAdj G (markedEdgeWeight a b z)) p)) *
          PowerSeries.map markConstHom
            (pathComplementDenominator G p a b z)) =
      (X : R⟦X⟧) ^ (p.list.length - 1) *
        C (walkWeight G s t z (pathWalkOfChain G p hchain)) *
        pathComplementDenominator G p a b z := by
  rw [markedCoeffSeries_path_term,
    pathMatrixWeight_weightedAdj_eq_walkWeight G p hchain a b z]
  change
    (X : R⟦X⟧) ^ (p.list.length - 1) *
        C (markedCoeff
          (((pathWalkOfChain G p hchain).edges.map
            (markedEdgeWeight a b z)).prod)) *
        pathComplementDenominator G p a b z =
      (X : R⟦X⟧) ^ (p.list.length - 1) *
        C ((pathWalkOfChain G p hchain).edges.map z).prod *
        pathComplementDenominator G p a b z
  rw [marked_product_coefficient a b hab z]
  have ha' :
      (pathWalkOfChain G p hchain).edges.count a = 1 := by
    rw [← pathCycleEdges_count_eq_walk_count G p hchain]
    exact ha
  have hb' :
      (pathWalkOfChain G p hchain).edges.count b = 1 := by
    rw [← pathCycleEdges_count_eq_walk_count G p hchain]
    exact hb
  simp [ha', hb']

theorem markedCoeffSeries_path_term_of_chain_general
    (hab : a ≠ b)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : DirectedPathList s t) (hchain : p.list.IsChain G.Adj)
    (z : Sym2 V → R) :
    markedCoeffSeries
        (((X : (Marked R)⟦X⟧) ^ (p.list.length - 1) *
          C (pathMatrixWeight
            (weightedAdj G (markedEdgeWeight a b z)) p)) *
          PowerSeries.map markConstHom
            (pathComplementDenominator G p a b z)) =
      (X : R⟦X⟧) ^ (p.list.length - 1) *
        C (if
            (pathWalkOfChain G p hchain).edges.count a = 1 ∧
            (pathWalkOfChain G p hchain).edges.count b = 1 then
              walkWeight G s t z (pathWalkOfChain G p hchain) else 0) *
        pathComplementDenominator G p a b z := by
  rw [markedCoeffSeries_path_term,
    pathMatrixWeight_weightedAdj_eq_walkWeight G p hchain a b z]
  change
    (X : R⟦X⟧) ^ (p.list.length - 1) *
        C (markedCoeff
          (((pathWalkOfChain G p hchain).edges.map
            (markedEdgeWeight a b z)).prod)) *
        pathComplementDenominator G p a b z =
      (X : R⟦X⟧) ^ (p.list.length - 1) *
        C (if
            (pathWalkOfChain G p hchain).edges.count a = 1 ∧
            (pathWalkOfChain G p hchain).edges.count b = 1 then
              (pathWalkOfChain G p hchain).edges.map z |>.prod else 0) *
        pathComplementDenominator G p a b z
  rw [marked_product_coefficient a b hab z]

abbrev graphPathListTarget
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (a b : Sym2 V) (d : ℕ) (p : DirectedPathList s t) : Prop :=
  p.list.IsChain G.Adj ∧
    (pathCycleEdges p).count a = 1 ∧
    (pathCycleEdges p).count b = 1 ∧
    p.list.length - 1 = d

theorem markedCoeffSeries_path_term_coeff
    (hab : a ≠ b)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : DirectedPathList s t)
    (z : Sym2 V → R)
    (dStar d : ℕ) (hd : d ≤ dStar)
    (hmin : ∀ q : G.Walk s t,
      IsTargetPath (a := a) (b := b) q → dStar ≤ q.length) :
    PowerSeries.coeff d
        (markedCoeffSeries
          (((X : (Marked R)⟦X⟧) ^ (p.list.length - 1) *
            C (pathMatrixWeight
              (weightedAdj G (markedEdgeWeight a b z)) p)) *
            PowerSeries.map markConstHom
              (pathComplementDenominator G p a b z))) =
      if hp : graphPathListTarget G a b d p then
        walkWeight G s t z (pathWalkOfChain G p hp.1)
      else 0 := by
  classical
  by_cases hchain : p.list.IsChain G.Adj
  · by_cases ha : (pathCycleEdges p).count a = 1
    · by_cases hb : (pathCycleEdges p).count b = 1
      · have hterm :=
          markedCoeffSeries_path_term_of_chain hab G p hchain ha hb z
        rw [hterm]
        have ha' :
            (pathWalkOfChain G p hchain).edges.count a = 1 := by
          rw [← pathCycleEdges_count_eq_walk_count G p hchain]
          exact ha
        have hb' :
            (pathWalkOfChain G p hchain).edges.count b = 1 := by
          rw [← pathCycleEdges_count_eq_walk_count G p hchain]
          exact hb
        have hmin' :
            dStar ≤ p.list.length - 1 := by
          have htarget :
              IsTargetPath (a := a) (b := b)
                (pathWalkOfChain G p hchain) :=
            ⟨pathWalkOfChain_isPath G p hchain, ha', hb'⟩
          have h := hmin (pathWalkOfChain G p hchain) htarget
          simpa [pathWalkOfChain_length G p hchain] using h
        rw [mul_assoc, PowerSeries.coeff_X_pow_mul']
        by_cases hn : p.list.length - 1 ≤ d
        · rw [if_pos hn]
          by_cases hnd : p.list.length - 1 = d
          · have hzero : d - (p.list.length - 1) = 0 := by omega
            rw [hzero, PowerSeries.coeff_C_mul,
              pathComplementDenominator_constant_one, mul_one]
            simp [graphPathListTarget, hchain, ha, hb, hnd]
          · exfalso
            omega
        · have hne : p.list.length - 1 ≠ d := by omega
          rw [if_neg hn]
          simp [graphPathListTarget, hchain, ha, hb, hne]
      · have htermzero :
            markedCoeffSeries
              (((X : (Marked R)⟦X⟧) ^ (p.list.length - 1) *
                C (pathMatrixWeight
                  (weightedAdj G (markedEdgeWeight a b z)) p)) *
                PowerSeries.map markConstHom
                  (pathComplementDenominator G p a b z)) = 0 := by
          rw [markedCoeffSeries_path_term_of_chain_general hab G p hchain z]
          have hb' :
              (pathWalkOfChain G p hchain).edges.count b ≠ 1 := by
            intro h
            apply hb
            rw [← pathCycleEdges_count_eq_walk_count G p hchain] at h
            exact h
          simp [hb']
        rw [htermzero]
        have hnot : ¬ graphPathListTarget G a b d p := by
          intro hp
          exact hb hp.2.2.1
        simp [hnot]
    · have htermzero :
          markedCoeffSeries
            (((X : (Marked R)⟦X⟧) ^ (p.list.length - 1) *
              C (pathMatrixWeight
                (weightedAdj G (markedEdgeWeight a b z)) p)) *
              PowerSeries.map markConstHom
                (pathComplementDenominator G p a b z)) = 0 := by
        rw [markedCoeffSeries_path_term_of_chain_general hab G p hchain z]
        have ha' :
            (pathWalkOfChain G p hchain).edges.count a ≠ 1 := by
          intro h
          apply ha
          rw [← pathCycleEdges_count_eq_walk_count G p hchain] at h
          exact h
        simp [ha']
      rw [htermzero]
      have hnot : ¬ graphPathListTarget G a b d p := by
        intro hp
        exact ha hp.2.1
      simp [hnot]
  · have htermzero :
        markedCoeffSeries
          (((X : (Marked R)⟦X⟧) ^ (p.list.length - 1) *
            C (pathMatrixWeight
              (weightedAdj G (markedEdgeWeight a b z)) p)) *
            PowerSeries.map markConstHom
              (pathComplementDenominator G p a b z)) = 0 := by
      rw [pathMatrixWeight_zero_of_not_chain G p a b z hchain]
      simp
      apply PowerSeries.ext
      intro n
      simp [markedCoeffSeries, markedCoeff]
    rw [htermzero]
    have hnot : ¬ graphPathListTarget G a b d p := by
      intro hp
      exact hchain hp.1
    simp [hnot]

abbrev targetPathSubtype
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (a b : Sym2 V) (d : ℕ) :=
  {p : G.Walk s t // p ∈ targetPaths G s t a b d}

abbrev graphPathListTargetSubtype
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (a b : Sym2 V) (d : ℕ) :=
  {p : DirectedPathList s t // graphPathListTarget G a b d p}

theorem graphPathListTarget_to_targetPath
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (a b : Sym2 V) (d : ℕ)
    (p : DirectedPathList s t)
    (hp : graphPathListTarget G a b d p) :
    pathWalkOfChain G p hp.1 ∈ targetPaths G s t a b d := by
  rcases hp with ⟨hchain, ha, hb, hlen⟩
  unfold targetPaths targetWalks
  apply Finset.mem_filter.mpr
  refine ⟨?_, pathWalkOfChain_isPath G p hchain⟩
  apply Finset.mem_filter.mpr
  refine ⟨?_, ?_, ?_⟩
  · apply Finset.mem_coe.mpr
    have hset :
        pathWalkOfChain G p hchain ∈
          (G.finsetWalkLength d s t : Set (G.Walk s t)) := by
      rw [SimpleGraph.coe_finsetWalkLength_eq]
      exact (pathWalkOfChain_length G p hchain).trans hlen
    exact Finset.mem_coe.mp hset
  · rw [← pathCycleEdges_count_eq_walk_count G p hchain]
    exact ha
  · rw [← pathCycleEdges_count_eq_walk_count G p hchain]
    exact hb

theorem targetPath_to_graphPathListTarget
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (a b : Sym2 V) (d : ℕ)
    (p : targetPathSubtype (s := s) (t := t) G a b d)
    (hpos : 0 < p.1.length) :
    graphPathListTarget G a b d
      (directedPathListOfWalk G p.1
        (Finset.mem_filter.mp p.2 |>.2) hpos) := by
  let q := p.1
  let hp : q.IsPath := Finset.mem_filter.mp p.2 |>.2
  let r := directedPathListOfWalk G q hp hpos
  have hchain : r.list.IsChain G.Adj :=
    directedPathListOfWalk_chain G q hp hpos
  have hround :
      pathWalkOfChain G r hchain = q :=
    pathWalkOfChain_of_directedPathListOfWalk G
      (p := q) hp hpos
  have htarget := Finset.mem_filter.mp p.2
  have hwalk := Finset.mem_filter.mp htarget.1
  have hpath := htarget.2
  have hlen : q.length = d := by
    have hset : q ∈ (G.finsetWalkLength d s t : Set (G.Walk s t)) :=
      Finset.mem_coe.mpr hwalk.1
    rw [SimpleGraph.coe_finsetWalkLength_eq] at hset
    exact hset
  have htarget' : p.1 ∈ targetPaths G s t a b d := p.2
  have hp' : p.1.IsPath := (Finset.mem_filter.mp htarget').2
  have hr :
      r = directedPathListOfWalk G p.1 hp' hpos := by
    rfl
  rw [← hr]
  refine ⟨hchain, ?_, ?_, ?_⟩
  · rw [pathCycleEdges_count_eq_walk_count G r hchain, hround]
    exact hwalk.2.1
  · rw [pathCycleEdges_count_eq_walk_count G r hchain, hround]
    exact hwalk.2.2
  · calc
      r.list.length - 1 =
          (pathWalkOfChain G r hchain).length :=
        (pathWalkOfChain_length G r hchain).symm
      _ = q.length := congrArg SimpleGraph.Walk.length hround
      _ = d := hlen

def graphPathListTargetEquiv
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (a b : Sym2 V) (d : ℕ) :
    graphPathListTargetSubtype (s := s) (t := t) G a b d ≃
      targetPathSubtype (s := s) (t := t) G a b d where
  toFun p :=
    ⟨pathWalkOfChain G p.1 p.2.1,
      graphPathListTarget_to_targetPath G a b d p.1 p.2⟩
  invFun q :=
    let hpos : 0 < q.1.length := by
      have htarget := Finset.mem_filter.mp q.2
      have hwalk := Finset.mem_filter.mp htarget.1
      have ha := hwalk.2.1
      have hlen : q.1.edges.length = q.1.length := q.1.length_edges
      have hcount : q.1.edges.count a ≤ q.1.edges.length :=
        List.count_le_length
      rw [ha, hlen] at hcount
      omega
    ⟨directedPathListOfWalk G q.1 (Finset.mem_filter.mp q.2 |>.2) hpos,
      targetPath_to_graphPathListTarget G a b d q hpos⟩
  left_inv p := by
    apply Subtype.ext
    exact directedPathListOfWalk_pathWalkOfChain G p.1 p.2.1
  right_inv q := by
    apply Subtype.ext
    let hpos : 0 < q.1.length := by
      have htarget := Finset.mem_filter.mp q.2
      have hwalk := Finset.mem_filter.mp htarget.1
      have ha := hwalk.2.1
      have hlen : q.1.edges.length = q.1.length := q.1.length_edges
      have hcount : q.1.edges.count a ≤ q.1.edges.length :=
        List.count_le_length
      rw [ha, hlen] at hcount
      omega
    exact pathWalkOfChain_of_directedPathListOfWalk G
      (p := q.1) (Finset.mem_filter.mp q.2 |>.2) hpos

theorem marked_cofactor_path_expansion
    (h₂ : ∀ x : R, x + x = 0)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s t : V) (hst : s ≠ t)
    (a b : Sym2 V) (hab : a ≠ b) (z : Sym2 V → R) :
    (matrixResolvent (weightedAdj G (markedEdgeWeight a b z))).adjugate s t =
      ∑ p : DirectedPathList s t,
        (X ^ (p.list.length - 1) *
          C (pathMatrixWeight (weightedAdj G (markedEdgeWeight a b z)) p)) *
          PowerSeries.map markConstHom
            (pathComplementDenominator G p a b z) := by
  let M := weightedAdj G (markedEdgeWeight a b z)
  have h₂marked : ∀ x : Marked R, x + x = 0 := by
    intro x
    ext <;> simp [h₂]
  have h₂series : ∀ x : (Marked R)⟦X⟧, x + x = 0 := by
    intro x
    apply PowerSeries.ext
    intro n
    simpa only [map_add, map_zero] using h₂marked (PowerSeries.coeff n x)
  rw [cofactor_path_complement_expansion h₂series
    (matrixResolvent M) hst]
  apply Fintype.sum_congr
  intro p
  rw [pathCycleWeight_resolvent h₂marked M p]
  congr 1
  exact complement_marked_det_is_const h₂ G p a b hab z

theorem markedCoeffSeries_sum
    {ι : Type*} [Fintype ι] (f : ι → (Marked R)⟦X⟧) :
    markedCoeffSeries (∑ i, f i) =
      ∑ i, markedCoeffSeries (f i) := by
  apply PowerSeries.ext
  intro n
  rw [markedCoeffSeries_coeff, map_sum]
  rw [map_sum]
  simp only [markedCoeffSeries_coeff]
  change
    (markedCoeffHom (R := R))
      (∑ i, PowerSeries.coeff n (f i)) =
    ∑ i, (markedCoeffHom (R := R))
      (PowerSeries.coeff n (f i))
  rw [map_sum]

theorem graphPathListTarget_sum_eq_pathSum
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (a b : Sym2 V) (z : Sym2 V → R) (d : ℕ) :
    (∑ p : DirectedPathList s t,
      if hp : graphPathListTarget G a b d p then
        walkWeight G s t z (pathWalkOfChain G p hp.1)
      else 0) =
      pathSum' (G := G) (s := s) (t := t) (a := a) (b := b) z d := by
  classical
  have hsplit := Finset.sum_dite
    (s := (Finset.univ : Finset (DirectedPathList s t)))
    (p := graphPathListTarget G a b d)
    (fun p hp => walkWeight G s t z (pathWalkOfChain G p hp.1))
    (fun _ _ => (0 : R))
  let good : Finset (DirectedPathList s t) :=
    Finset.univ.filter (graphPathListTarget G a b d)
  let bad : Finset (DirectedPathList s t) :=
    Finset.univ.filter (fun p => ¬ graphPathListTarget G a b d p)
  let e : good ≃ graphPathListTargetSubtype (s := s) (t := t) G a b d :=
    Equiv.subtypeEquivProp (by
      funext p
      apply propext
      simp [good])
  calc
    (∑ p : DirectedPathList s t,
      if hp : graphPathListTarget G a b d p then
        walkWeight G s t z (pathWalkOfChain G p hp.1)
      else 0) =
        (∑ p : good,
          walkWeight G s t z
            (pathWalkOfChain G p.1
              (Finset.mem_filter.mp p.2).2.1)) +
        (∑ p : bad, (0 : R)) := by
          exact hsplit
    _ = ∑ p : graphPathListTargetSubtype (s := s) (t := t) G a b d,
        walkWeight G s t z (pathWalkOfChain G p.1 p.2.1) := by
          simp only [Finset.sum_const_zero, add_zero]
          apply Fintype.sum_equiv e
          intro p
          rfl
    _ = _ := by
      calc
        (∑ p : graphPathListTargetSubtype (s := s) (t := t) G a b d,
            walkWeight G s t z (pathWalkOfChain G p.1 p.2.1)) =
          ∑ q : targetPathSubtype (s := s) (t := t) G a b d,
            walkWeight G s t z q.1 := by
              apply Fintype.sum_equiv (graphPathListTargetEquiv
                (s := s) (t := t) G a b d)
              intro p
              rfl
        _ = pathSum' (G := G) (s := s) (t := t)
            (a := a) (b := b) z d := by
              unfold pathSum'
              exact (Finset.sum_subtype (targetPaths G s t a b d)
                (fun q => Iff.rfl) (walkWeight G s t z)).symm

theorem determinantNumerator_coeff_eq_pathSum_of_minimal
    (h₂ : ∀ x : R, x + x = 0)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s t : V) (hst : s ≠ t)
    (a b : Sym2 V) (hab : a ≠ b) (z : Sym2 V → R)
    (dStar d : ℕ) (hd : d ≤ dStar)
    (hmin : ∀ q : G.Walk s t,
      IsTargetPath (a := a) (b := b) q → dStar ≤ q.length) :
    PowerSeries.coeff d (determinantNumerator G s t a b z) =
      pathSum' (G := G) (s := s) (t := t)
        (a := a) (b := b) z d := by
  unfold determinantNumerator
  rw [marked_cofactor_path_expansion h₂ G s t hst a b hab z,
    markedCoeffSeries_sum, map_sum]
  calc
    (∑ p : DirectedPathList s t,
        PowerSeries.coeff d
          (markedCoeffSeries
            (((X : (Marked R)⟦X⟧) ^ (p.list.length - 1) *
              C (pathMatrixWeight
                (weightedAdj G (markedEdgeWeight a b z)) p)) *
              PowerSeries.map markConstHom
                (pathComplementDenominator G p a b z)))) =
      ∑ p : DirectedPathList s t,
        if hp : graphPathListTarget G a b d p then
          walkWeight G s t z (pathWalkOfChain G p hp.1)
        else 0 := by
          apply Finset.sum_congr rfl
          intro p _
          exact markedCoeffSeries_path_term_coeff
            hab G p z dStar d hd hmin
    _ = pathSum' (G := G) (s := s) (t := t)
        (a := a) (b := b) z d :=
      graphPathListTarget_sum_eq_pathSum G a b z d

end
end TwoDoorsProof
