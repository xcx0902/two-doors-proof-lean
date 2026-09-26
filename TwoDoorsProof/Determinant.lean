import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.RowCol
import Mathlib.RingTheory.Polynomial.Basic

/-!
# The marked directed edge in the determinant argument

Adding a *directed* formal edge in position `(t,s)` is a rank-one change, even
if the original symmetric adjacency matrix already has a nonzero `(t,s)`
entry. The coefficient of its independent weight is the cofactor `(t,s)`,
which is the `(s,t)` entry of the adjugate.
-/

namespace TwoDoorsProof

open Matrix

variable {V R : Type*} [Fintype V] [DecidableEq V] [CommRing R]

def permMonomial (A : Matrix V V R) (σ : Equiv.Perm V) : R :=
  ∏ i, A (σ i) i

def nonInvolutivePerms : Finset (Equiv.Perm V) :=
  Finset.univ.filter fun σ => σ⁻¹ ≠ σ

theorem permMonomial_inv (A : Matrix V V R) (σ : Equiv.Perm V)
    (hsymm : ∀ i j, A i j = A j i) :
    permMonomial A σ⁻¹ = permMonomial A σ := by
  unfold permMonomial
  calc
    (∏ i, A (σ⁻¹ i) i) =
        ∏ i, A i (σ i) := by
      apply Fintype.prod_equiv σ⁻¹
      intro i
      simp
    _ = ∏ i, A (σ i) i := by
      apply Finset.prod_congr rfl
      intro i hi
      exact hsymm _ _

theorem nonInvolutive_perm_sum_zero (h₂ : ∀ x : R, x + x = 0)
    (A : Matrix V V R) (hsymm : ∀ i j, A i j = A j i) :
    ∑ σ ∈ nonInvolutivePerms (V := V), permMonomial A σ = 0 := by
  apply Finset.sum_involution (fun σ _ => σ⁻¹)
  · intro σ hσ
    rw [permMonomial_inv A σ hsymm]
    exact h₂ _
  · intro σ hσ _
    exact Finset.mem_filter.mp hσ |>.2
  · intro σ hσ
    exact inv_inv σ
  · intro σ hσ
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, by
      simpa [eq_comm] using Finset.mem_filter.mp hσ |>.2⟩

def involutivePerms : Finset (Equiv.Perm V) :=
  Finset.univ.filter fun σ => σ⁻¹ = σ

theorem det_eq_perm_sum_charTwo (h₂ : ∀ x : R, x + x = 0)
    (A : Matrix V V R) :
    A.det = ∑ σ, permMonomial A σ := by
  have hneg : (-1 : R) = 1 := by
    have h := h₂ (1 : R)
    calc
      (-1 : R) = -(1 + 1) + 1 := by abel
      _ = -0 + 1 := by rw [h]
      _ = 1 := by simp
  rw [Matrix.det_apply']
  apply Finset.sum_congr rfl
  intro σ hσ
  unfold permMonomial
  obtain hs | hs := Int.units_eq_one_or (Equiv.Perm.sign σ)
  · simp [hs]
  · rw [hs]
    simp [hneg]

theorem det_eq_involutive_perm_sum (h₂ : ∀ x : R, x + x = 0)
    (A : Matrix V V R) (hsymm : ∀ i j, A i j = A j i) :
    A.det = ∑ σ ∈ involutivePerms (V := V), permMonomial A σ := by
  rw [det_eq_perm_sum_charTwo h₂]
  have hpart :
      (Finset.univ : Finset (Equiv.Perm V)) =
        involutivePerms (V := V) ∪ nonInvolutivePerms (V := V) := by
    ext σ
    by_cases h : σ⁻¹ = σ
    · simp [involutivePerms, nonInvolutivePerms, h]
    · simp [involutivePerms, nonInvolutivePerms, h,
        show ¬σ = σ⁻¹ from fun hs => h hs.symm]
  have hdisj : Disjoint (involutivePerms (V := V))
      (nonInvolutivePerms (V := V)) := by
    apply Finset.disjoint_left.mpr
    intro σ hσ hσ'
    exact Finset.mem_filter.mp hσ' |>.2 (Finset.mem_filter.mp hσ |>.2)
  rw [hpart, Finset.sum_union hdisj,
    nonInvolutive_perm_sum_zero h₂ A hsymm, add_zero]

private theorem involutive_perm_monomial_zero_of_pair
    (A : Matrix V V R) (σ : Equiv.Perm V)
    (hσ : σ⁻¹ = σ) (i : V) (hi : σ i ≠ i)
    (hzero : A (σ i) i * A i (σ i) = 0) :
    permMonomial A σ = 0 := by
  let j := σ i
  have hij : i ≠ j := Ne.symm hi
  have hji : σ j = i := by
    dsimp [j]
    have h := σ.symm_apply_apply i
    change σ.symm = σ at hσ
    rw [hσ] at h
    exact h
  unfold permMonomial
  have hsub : ({i, j} : Finset V) ⊆ Finset.univ := Finset.subset_univ _
  rw [← Finset.prod_sdiff hsub, Finset.prod_pair hij]
  rw [hji]
  change (∏ x ∈ Finset.univ \ {i, j}, A (σ x) x) *
    (A (σ i) i * A i (σ i)) = 0
  rw [hzero, mul_zero]

theorem involutive_perm_monomial_eq_of_square_zero_difference
    (A B : Matrix V V R) (σ : Equiv.Perm V)
    (hσ : σ⁻¹ = σ)
    (hdiag : ∀ i, A i i = B i i)
    (hzero : ∀ i j, A i j ≠ B i j →
      A i j * A j i = 0 ∧ B i j * B j i = 0) :
    permMonomial A σ = permMonomial B σ := by
  by_cases hsame : ∀ i, A (σ i) i = B (σ i) i
  · unfold permMonomial
    exact Finset.prod_congr rfl (fun i _ => hsame i)
  · obtain ⟨i, hi⟩ := not_forall.mp hsame
    have hne : σ i ≠ i := by
      intro heq
      exact hi (by simpa only [heq] using hdiag i)
    obtain ⟨ha, hb⟩ := hzero (σ i) i hi
    rw [involutive_perm_monomial_zero_of_pair A σ hσ i hne ha,
      involutive_perm_monomial_zero_of_pair B σ hσ i hne hb]

theorem det_eq_of_symmetric_square_zero_difference
    (h₂ : ∀ x : R, x + x = 0)
    (A B : Matrix V V R)
    (hA : ∀ i j, A i j = A j i)
    (hB : ∀ i j, B i j = B j i)
    (hdiag : ∀ i, A i i = B i i)
    (hzero : ∀ i j, A i j ≠ B i j →
      A i j * A j i = 0 ∧ B i j * B j i = 0) :
    A.det = B.det := by
  rw [det_eq_involutive_perm_sum h₂ A hA,
    det_eq_involutive_perm_sum h₂ B hB]
  apply Finset.sum_congr rfl
  intro σ hσ
  exact involutive_perm_monomial_eq_of_square_zero_difference A B σ
    (Finset.mem_filter.mp hσ).2 hdiag hzero

theorem det_add_directed_edge (Q : Matrix V V R) (s t : V) (y : R) :
    (Q + Matrix.single t s y).det = Q.det + y * Q.adjugate s t := by
  have hrow : Q + Matrix.single t s y =
      Q.updateRow t (Q t + Pi.single s y) := by
    ext i j
    by_cases hi : i = t
    · subst i
      simp [Matrix.single_apply, Matrix.updateRow_apply, Pi.single_apply, eq_comm]
    · have ht : t ≠ i := Ne.symm hi
      simp [Matrix.updateRow_apply, hi, ht]
  rw [hrow, Matrix.det_updateRow_add, Matrix.updateRow_eq_self]
  have hs : (Pi.single s y : V → R) = y • Pi.single s 1 := by
    ext i
    simp [Pi.single_apply, smul_eq_mul, mul_ite]
  rw [hs, Matrix.det_updateRow_smul, Matrix.adjugate_apply]

theorem marked_determinant_coeff_one (Q : Matrix V V R) (s t : V) :
    (Matrix.det (Q.map Polynomial.C + Matrix.single t s Polynomial.X)).coeff 1 =
      Q.adjugate s t := by
  have h := det_add_directed_edge (R := Polynomial R) (Q.map Polynomial.C)
    s t Polynomial.X
  have h' := congrArg (fun p : Polynomial R => p.coeff 1) h
  have hmap (M : Matrix V V R) :
      (M.map Polynomial.C).det = Polynomial.C M.det := by
    simpa using (RingHom.map_det (Polynomial.C : R →+* Polynomial R) M).symm
  have hdet0 : (Q.map Polynomial.C).det.coeff 1 = 0 := by
    rw [hmap]
    simp
  have hrow :
      (Q.map Polynomial.C).updateRow t (Pi.single s 1) =
        (Q.updateRow t (Pi.single s 1)).map Polynomial.C := by
    ext i j
    by_cases hi : i = t
    · subst i
      by_cases hj : s = j <;> simp [Matrix.updateRow_apply, Pi.single_apply, hj]
    · simp [Matrix.updateRow_apply, hi]
  have hrowdet :
      ((Q.map Polynomial.C).updateRow t (Pi.single s 1)).det.coeff 0 =
        (Q.updateRow t (Pi.single s 1)).det := by
    rw [hrow, hmap]
    simp
  rw [Matrix.adjugate_apply] at h'
  rw [Polynomial.coeff_add, Polynomial.coeff_X_mul, hdet0, hrowdet, zero_add] at h'
  simpa [Matrix.adjugate_apply] using h'

/-- The adjugate identity used before expanding the determinant into cycles.
No nonsingularity is assumed: this is an identity over any commutative ring. -/
theorem resolvent_cofactor (Q : Matrix V V R) (s t : V) :
    Q.det * Q.adjugate s t =
      (Q + Matrix.single t s 1).det * Q.det - Q.det ^ 2 := by
  rw [det_add_directed_edge]
  ring

end TwoDoorsProof
