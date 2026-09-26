import TwoDoorsProof.MatrixSeries
import Mathlib.Algebra.CharP.Two

namespace TwoDoorsProof

open Matrix PowerSeries SimpleGraph
open scoped Matrix
noncomputable section

variable {V R : Type*} [DecidableEq V] [Fintype V] [CommRing R]

theorem resolvent_apply_offdiag (M : Matrix V V R)
    {i j : V} (hij : i ≠ j) :
    matrixResolvent M i j = -(PowerSeries.X * PowerSeries.C (M i j)) := by
  simp [matrixResolvent, seriesMatrix, Matrix.one_apply, hij, smul_eq_mul]

theorem resolvent_apply_diag (M : Matrix V V R) (i : V)
    (hzero : M i i = 0) :
    matrixResolvent M i i = 1 := by
  simp [matrixResolvent, seriesMatrix, Matrix.one_apply, hzero]

theorem resolvent_symmetric (M : Matrix V V R)
    (hM : ∀ i j, M i j = M j i) :
    ∀ i j, matrixResolvent M i j = matrixResolvent M j i := by
  intro i j
  simp [matrixResolvent, seriesMatrix, Matrix.one_apply, eq_comm, hM i j]

theorem weightedAdj_symmetric (G : SimpleGraph V) [DecidableRel G.Adj]
    (z : Sym2 V → R) :
    ∀ i j, weightedAdj G z i j = weightedAdj G z j i := by
  intro i j
  by_cases hij : G.Adj i j
  · simp [weightedAdj, hij, G.adj_comm, Sym2.eq_swap]
  · simp [weightedAdj, hij, G.adj_comm]

theorem weightedAdj_diag (G : SimpleGraph V) [DecidableRel G.Adj]
    (z : Sym2 V → R) (i : V) :
    weightedAdj G z i i = 0 := by
  simp [weightedAdj, G.loopless.irrefl]

theorem resolvent_sq_zero_offdiag
    (M : Matrix V V R) (i j : V) (hij : i ≠ j)
    (hzero : M i j * M j i = 0) :
    matrixResolvent M i j * matrixResolvent M j i = 0 := by
  rw [resolvent_apply_offdiag M hij,
    resolvent_apply_offdiag M (Ne.symm hij)]
  calc
    -(X * C (M i j)) * -(X * C (M j i)) =
        X ^ 2 * C (M i j * M j i) := by
          rw [map_mul]
          ring
    _ = 0 := by rw [hzero, map_zero, mul_zero]

def ordinaryMarkedEdgeWeight {E : Type*} [DecidableEq E]
    (a b : E) (z : E → R) (e : E) : Marked R :=
  if e = a ∨ e = b then 0 else markConst (z e)

theorem markedEdgeWeight_eq_ordinary_of_not_special
    {E : Type*} [DecidableEq E]
    (a b : E) (z : E → R) (e : E)
    (ha : e ≠ a) (hb : e ≠ b) :
    markedEdgeWeight a b z e = ordinaryMarkedEdgeWeight a b z e := by
  rw [markedEdgeWeight_eq_const a b e z ha hb]
  simp [ordinaryMarkedEdgeWeight, ha, hb]

theorem markedEdgeWeight_sq_zero_of_difference
    {E : Type*} [DecidableEq E]
    (a b : E) (hab : a ≠ b) (z : E → R) (e : E)
    (hne : markedEdgeWeight a b z e ≠ ordinaryMarkedEdgeWeight a b z e) :
    (markedEdgeWeight a b z e) ^ 2 = 0 ∧
      ordinaryMarkedEdgeWeight a b z e = 0 := by
  have hspec : e = a ∨ e = b := by
    by_contra h
    push_neg at h
    exact hne (markedEdgeWeight_eq_ordinary_of_not_special a b z e h.1 h.2)
  exact ⟨markedEdgeWeight_sq_special a b hab z e hspec,
    by simp [ordinaryMarkedEdgeWeight, hspec]⟩

theorem marked_denominator_eq_ordinary
    [CharP R 2] (G : SimpleGraph V) [DecidableRel G.Adj]
    (a b : Sym2 V) (hab : a ≠ b) (z : Sym2 V → R) :
    (matrixResolvent (weightedAdj G (markedEdgeWeight a b z))).det =
      (matrixResolvent (weightedAdj G
        (ordinaryMarkedEdgeWeight a b z))).det := by
  let M := weightedAdj G (markedEdgeWeight a b z)
  let N := weightedAdj G (ordinaryMarkedEdgeWeight a b z)
  let A := matrixResolvent M
  let B := matrixResolvent N
  have hM : ∀ i j, M i j = M j i :=
    weightedAdj_symmetric G (markedEdgeWeight a b z)
  have hN : ∀ i j, N i j = N j i :=
    weightedAdj_symmetric G (ordinaryMarkedEdgeWeight a b z)
  have h₂marked : ∀ x : Marked R, x + x = 0 := by
    intro x
    ext <;> simp [CharTwo.add_self_eq_zero]
  have h₂series : ∀ x : (Marked R)⟦X⟧, x + x = 0 := by
    intro x
    apply PowerSeries.ext
    intro n
    simpa only [map_add, map_zero] using h₂marked (PowerSeries.coeff n x)
  have hdiag : ∀ i, A i i = B i i := by
    intro i
    change matrixResolvent M i i = matrixResolvent N i i
    have hm : M i i = 0 := weightedAdj_diag G (markedEdgeWeight a b z) i
    have hn : N i i = 0 := weightedAdj_diag G (ordinaryMarkedEdgeWeight a b z) i
    rw [resolvent_apply_diag M i hm, resolvent_apply_diag N i hn]
  change A.det = B.det
  apply det_eq_of_symmetric_square_zero_difference h₂series A B
    (resolvent_symmetric M hM) (resolvent_symmetric N hN) hdiag
  intro i j hneq
  have hij : i ≠ j := by
    intro heq
    subst j
    exact hneq (hdiag i)
  have hadj : G.Adj i j := by
    by_contra h
    apply hneq
    simp [A, B, resolvent_apply_offdiag, hij,
      M, N, weightedAdj, h]
  have hweight : markedEdgeWeight a b z s(i, j) ≠
      ordinaryMarkedEdgeWeight a b z s(i, j) := by
    intro heq
    apply hneq
    change matrixResolvent M i j = matrixResolvent N i j
    rw [resolvent_apply_offdiag M hij, resolvent_apply_offdiag N hij]
    simp [M, N, weightedAdj, hadj, heq]
  obtain ⟨hsq, hnzero⟩ :=
    markedEdgeWeight_sq_zero_of_difference a b hab z s(i, j) hweight
  have hmzero : M i j * M j i = 0 := by
    rw [← hM i j]
    simpa [M, weightedAdj, hadj, pow_two] using hsq
  have hnzero' : N i j = 0 := by
    simpa [N, weightedAdj, hadj] using hnzero
  constructor
  · exact resolvent_sq_zero_offdiag M i j hij hmzero
  · change matrixResolvent N i j * matrixResolvent N j i = 0
    rw [resolvent_apply_offdiag N hij, hnzero']
    simp

theorem resolvent_det_constant_one (M : Matrix V V R) :
    PowerSeries.coeff 0 (matrixResolvent M).det = 1 := by
  let c : R⟦X⟧ →+* R := PowerSeries.constantCoeff
  have hmatrix : (matrixResolvent M).map c = (1 : Matrix V V R) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [c, matrixResolvent, seriesMatrix]
    · simp [c, matrixResolvent, seriesMatrix, hij]
  calc
    PowerSeries.coeff 0 (matrixResolvent M).det =
        c (matrixResolvent M).det := by
          exact PowerSeries.coeff_zero_eq_constantCoeff_apply _
    _ = ((matrixResolvent M).map c).det :=
      RingHom.map_det c (matrixResolvent M)
    _ = 1 := by rw [hmatrix, Matrix.det_one]

def ordinaryEdgeWeight {E : Type*} [DecidableEq E]
    (a b : E) (z : E → R) (e : E) : R :=
  if e = a ∨ e = b then 0 else z e

theorem ordinaryMarkedEdgeWeight_eq_map {E : Type*} [DecidableEq E]
    (a b : E) (z : E → R) (e : E) :
    ordinaryMarkedEdgeWeight a b z e =
      markConstHom (ordinaryEdgeWeight a b z e) := by
  change ordinaryMarkedEdgeWeight a b z e =
    markConst (ordinaryEdgeWeight a b z e)
  by_cases h : e = a ∨ e = b <;>
    simp [ordinaryMarkedEdgeWeight, ordinaryEdgeWeight, h, markConst]

theorem ordinaryMarkedAdj_eq_map (G : SimpleGraph V) [DecidableRel G.Adj]
    (a b : Sym2 V) (z : Sym2 V → R) :
    weightedAdj G (ordinaryMarkedEdgeWeight a b z) =
      (weightedAdj G (ordinaryEdgeWeight a b z)).map markConstHom := by
  apply Matrix.ext
  intro i j
  by_cases hadj : G.Adj i j
  · simp [weightedAdj, hadj, ordinaryMarkedEdgeWeight_eq_map]
  · simp [weightedAdj, hadj]

theorem resolvent_map {S : Type*} [CommRing S]
    (f : R →+* S) (M : Matrix V V R) :
    (matrixResolvent M).map (PowerSeries.map f) =
      matrixResolvent (M.map f) := by
  apply Matrix.ext
  intro i j
  by_cases hij : i = j
  · subst j
    simp [matrixResolvent, seriesMatrix, PowerSeries.map_C,
      PowerSeries.map_X]
  · simp [matrixResolvent, seriesMatrix, hij, PowerSeries.map_C,
      PowerSeries.map_X]

theorem ordinary_denominator_eq_map (G : SimpleGraph V) [DecidableRel G.Adj]
    (a b : Sym2 V) (z : Sym2 V → R) :
    (matrixResolvent (weightedAdj G
      (ordinaryMarkedEdgeWeight a b z))).det =
    PowerSeries.map markConstHom
      (matrixResolvent (weightedAdj G
        (ordinaryEdgeWeight a b z))).det := by
  rw [ordinaryMarkedAdj_eq_map]
  have hres := resolvent_map (R := R) (S := Marked R) (markConstHom (R := R))
    (weightedAdj G (ordinaryEdgeWeight a b z))
  rw [← hres]
  simp [Matrix.det_apply', map_sum, map_prod]

end
end TwoDoorsProof
