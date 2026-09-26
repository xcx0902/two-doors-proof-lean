import TwoDoorsProof.PathCycleWeights

namespace TwoDoorsProof

open Matrix PowerSeries SimpleGraph
open scoped Matrix

noncomputable section

variable {V R : Type*} [DecidableEq V] [Fintype V] [CommRing R]

omit [DecidableEq V] [Fintype V] in
theorem weightedAdj_submatrix_induce
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : DirectedPathList s t) (z : Sym2 V → R) :
    (weightedAdj G z).submatrix
        (fun x : {x : V // x ∉ p.list} => (x : V))
        (fun x : {x : V // x ∉ p.list} => (x : V)) =
      (fun (x y : {x : V // x ∉ p.list}) =>
        if G.Adj (x : V) (y : V) then
          z s((x : V), (y : V)) else 0) := by
  ext x y
  simp [weightedAdj, Matrix.submatrix_apply]

theorem complement_marked_det_eq_ordinary
    (h₂ : ∀ x : R, x + x = 0)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : DirectedPathList s t) (a b : Sym2 V) (hab : a ≠ b)
    (z : Sym2 V → R) :
    ((matrixResolvent (weightedAdj G (markedEdgeWeight a b z))).submatrix
        (fun x : {x : V // x ∉ p.list} => (x : V))
        (fun x : {x : V // x ∉ p.list} => (x : V))).det =
      ((matrixResolvent (weightedAdj G
        (ordinaryMarkedEdgeWeight a b z))).submatrix
        (fun x : {x : V // x ∉ p.list} => (x : V))
        (fun x : {x : V // x ∉ p.list} => (x : V))).det := by
  let M := matrixResolvent (weightedAdj G (markedEdgeWeight a b z))
  let N := matrixResolvent (weightedAdj G (ordinaryMarkedEdgeWeight a b z))
  let A := M.submatrix
    (fun x : {x : V // x ∉ p.list} => (x : V))
    (fun x : {x : V // x ∉ p.list} => (x : V))
  let B := N.submatrix
    (fun x : {x : V // x ∉ p.list} => (x : V))
    (fun x : {x : V // x ∉ p.list} => (x : V))
  have h₂marked : ∀ x : Marked R, x + x = 0 := by
    intro x
    ext <;> simp [h₂]
  have h₂series : ∀ x : (Marked R)⟦X⟧, x + x = 0 := by
    intro x
    apply PowerSeries.ext
    intro n
    simpa only [map_add, map_zero] using h₂marked (PowerSeries.coeff n x)
  have hA : ∀ i j, A i j = A j i := by
    intro i j
    exact resolvent_symmetric _ (weightedAdj_symmetric G
      (markedEdgeWeight a b z)) _ _
  have hB : ∀ i j, B i j = B j i := by
    intro i j
    exact resolvent_symmetric _ (weightedAdj_symmetric G
      (ordinaryMarkedEdgeWeight a b z)) _ _
  have hdiag : ∀ i, A i i = B i i := by
    intro i
    change M (i : V) (i : V) = N (i : V) (i : V)
    rw [show M (i : V) (i : V) = 1 by
      exact resolvent_apply_diag
        (weightedAdj G (markedEdgeWeight a b z)) (i : V)
        (weightedAdj_diag G (markedEdgeWeight a b z) (i : V))]
    rw [show N (i : V) (i : V) = 1 by
      exact resolvent_apply_diag
        (weightedAdj G (ordinaryMarkedEdgeWeight a b z)) (i : V)
        (weightedAdj_diag G (ordinaryMarkedEdgeWeight a b z) (i : V))]
  apply det_eq_of_symmetric_square_zero_difference h₂series A B hA hB hdiag
  intro i j hneq
  have hij : (i : V) ≠ (j : V) := by
    intro heq
    apply hneq
    have hij' : i = j := Subtype.ext heq
    subst j
    exact hdiag i
  have hweight : markedEdgeWeight a b z s((i : V), (j : V)) ≠
      ordinaryMarkedEdgeWeight a b z s((i : V), (j : V)) := by
    intro heq
    apply hneq
    change matrixResolvent (weightedAdj G (markedEdgeWeight a b z))
        (i : V) (j : V) =
      matrixResolvent (weightedAdj G (ordinaryMarkedEdgeWeight a b z))
        (i : V) (j : V)
    rw [resolvent_apply_offdiag
      (weightedAdj G (markedEdgeWeight a b z)) hij,
      resolvent_apply_offdiag
        (weightedAdj G (ordinaryMarkedEdgeWeight a b z)) hij]
    simp [weightedAdj, heq]
  obtain ⟨hsq, hnzero⟩ :=
    markedEdgeWeight_sq_zero_of_difference a b hab z s(i, j) hweight
  have hmzero :
      (weightedAdj G (markedEdgeWeight a b z)) (i : V) (j : V) *
        (weightedAdj G (markedEdgeWeight a b z)) (j : V) (i : V) = 0 := by
    by_cases hadj : G.Adj (i : V) (j : V)
    · simpa [weightedAdj, hadj, G.adj_comm, Sym2.eq_swap, pow_two] using hsq
    · simp [weightedAdj, hadj]
  have hnzero' :
      (weightedAdj G (ordinaryMarkedEdgeWeight a b z)) (i : V) (j : V) = 0 := by
    by_cases hadj : G.Adj (i : V) (j : V)
    · simpa [weightedAdj, hadj] using hnzero
    · simp [weightedAdj, hadj]
  constructor
  · change M (i : V) (j : V) * M (j : V) (i : V) = 0
    exact resolvent_sq_zero_offdiag
      (weightedAdj G (markedEdgeWeight a b z))
      (i : V) (j : V) hij hmzero
  · change N (i : V) (j : V) * N (j : V) (i : V) = 0
    exact resolvent_sq_zero_offdiag
      (weightedAdj G (ordinaryMarkedEdgeWeight a b z))
      (i : V) (j : V) hij (by
        rw [hnzero']
        simp)

theorem complement_marked_det_is_const
    (h₂ : ∀ x : R, x + x = 0)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (p : DirectedPathList s t) (a b : Sym2 V) (hab : a ≠ b)
    (z : Sym2 V → R) :
    ((matrixResolvent (weightedAdj G (markedEdgeWeight a b z))).submatrix
      (fun x : {x : V // x ∉ p.list} => (x : V))
      (fun x : {x : V // x ∉ p.list} => (x : V))).det =
      PowerSeries.map markConstHom
        ((matrixResolvent (weightedAdj G (ordinaryEdgeWeight a b z))).submatrix
          (fun x : {x : V // x ∉ p.list} => (x : V))
          (fun x : {x : V // x ∉ p.list} => (x : V))).det := by
  let e := fun x : {x : V // x ∉ p.list} => (x : V)
  let Q : Matrix {x : V // x ∉ p.list} {x : V // x ∉ p.list} R⟦X⟧ :=
    (matrixResolvent (weightedAdj G (ordinaryEdgeWeight a b z))).submatrix e e
  change _ = PowerSeries.map markConstHom Q.det
  rw [complement_marked_det_eq_ordinary h₂ G p a b hab z]
  have hmap := resolvent_map (R := R) (S := Marked R)
    (markConstHom (R := R))
    (weightedAdj G (ordinaryEdgeWeight a b z))
  have hadj := ordinaryMarkedAdj_eq_map G a b z
  have hsub :
      (matrixResolvent (weightedAdj G
        (ordinaryMarkedEdgeWeight a b z))).submatrix e e =
        ((matrixResolvent (weightedAdj G
          (ordinaryEdgeWeight a b z))).submatrix e e).map
            (PowerSeries.map markConstHom) := by
    rw [hadj, ← hmap]
    apply Matrix.ext
    intro i j
    change PowerSeries.map markConstHom
        (matrixResolvent (weightedAdj G (ordinaryEdgeWeight a b z))
          (e i) (e j)) =
      PowerSeries.map markConstHom
        (matrixResolvent (weightedAdj G (ordinaryEdgeWeight a b z))
          (e i) (e j))
    rfl
  rw [hsub]
  simp [Q, Matrix.det_apply', map_sum, map_prod]

end
end TwoDoorsProof
