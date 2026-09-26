import TwoDoorsProof.FintypePath

namespace TwoDoorsProof

open Matrix

noncomputable section

variable {V R : Type*} [DecidableEq V] [Fintype V] [CommRing R]
variable {s t : V}

abbrev markedPerm (s t : V) :=
  {σ : Equiv.Perm V // σ t = s}

private theorem cast_complementPerm_apply
    {l₁ l₂ : List V} (h : l₁ = l₂)
    (τ : Equiv.Perm {x : V // x ∉ l₁})
    (x : {x : V // x ∉ l₂}) :
    ((cast (congrArg (fun l : List V =>
      Equiv.Perm {x : V // x ∉ l}) h) τ) x : V) =
      (τ ⟨x.1, by simpa [h] using x.2⟩ : V) := by
  cases h
  rfl

def pathComplementEquiv (hst : s ≠ t) :
    markedPerm s t ≃ Σ p : DirectedPathList s t, complementPerm p where
  toFun σ :=
    ⟨pathOfPerm σ.1 s t hst σ.2,
      restrictedPerm σ.1 s t hst σ.2⟩
  invFun p :=
    ⟨pathComplementPerm p.1 p.2,
      pathComplementPerm_marked p.1 p.2⟩
  left_inv σ := by
    apply Subtype.ext
    exact perm_eq_pathComplement σ.1 s t hst σ.2
  right_inv p := by
    let z : Σ p : DirectedPathList s t, complementPerm p :=
      ⟨pathOfPerm (pathComplementPerm p.1 p.2) s t hst
          (pathComplementPerm_marked p.1 p.2),
        restrictedPerm (pathComplementPerm p.1 p.2) s t hst
          (pathComplementPerm_marked p.1 p.2)⟩
    change z = p
    have hfst : z.fst = p.1 := by
      dsimp [z]
      exact pathOfPerm_pathComplement p.1 p.2 hst
    apply Sigma.ext hfst
    have hlist : z.fst.list = p.1.list := congrArg DirectedPathList.list hfst
    have htype : complementPerm z.fst = complementPerm p.1 := by
      unfold complementPerm
      rw [hlist]
    have htransport : cast htype z.snd = p.2 := by
      apply Equiv.ext
      intro x
      apply Subtype.ext
      have hcast := cast_complementPerm_apply hlist z.snd x
      change (cast htype z.snd x : V) = (p.2 x : V)
      rw [hcast]
      rw [restrictedPerm_apply
        (pathComplementPerm p.1 p.2) s t hst
        (pathComplementPerm_marked p.1 p.2)
        (by
          change (x : V) ∉ z.fst.list
          rw [hlist]
          exact x.property)]
      rw [pathComplementPerm_apply_of_not_mem p.1 p.2 x.property]
    exact (cast_heq htype z.snd).symm.trans (heq_of_eq htransport)

def cycleMonomial (A : Matrix V V R) (p : DirectedPathList s t) : R :=
  ∏ x ∈ p.list.toFinset, A (cycleOfPath p x) x

def complementMonomial (A : Matrix V V R)
    (p : DirectedPathList s t) (τ : complementPerm p) : R :=
  permMonomial
    (A.submatrix (fun x : {x : V // x ∉ p.list} => (x : V))
      (fun x : {x : V // x ∉ p.list} => (x : V))) τ

private def complementEquiv
    (p : DirectedPathList s t) :
    {x : V // x ∈ p.list.toFinsetᶜ} ≃ {x : V // x ∉ p.list} where
  toFun x := ⟨x.1, by
    intro hxmem
    exact (Finset.mem_compl.mp x.2) (by simpa using hxmem)⟩
  invFun x := ⟨x.1, by
    simpa using x.2⟩
  left_inv x := rfl
  right_inv x := rfl

theorem permMonomial_pathComplement
    (A : Matrix V V R) (p : DirectedPathList s t)
    (τ : complementPerm p) :
    permMonomial A (pathComplementPerm p τ) =
      cycleMonomial A p * complementMonomial A p τ := by
  let S : Finset V := p.list.toFinset
  have hsplit :
      (∏ x, A ((pathComplementPerm p τ) x) x) =
        (∏ x ∈ S, A ((pathComplementPerm p τ) x) x) *
          ∏ x ∈ Sᶜ, A ((pathComplementPerm p τ) x) x := by
    simpa [S] using
      (Finset.prod_mul_prod_compl S
        (fun x : V => A ((pathComplementPerm p τ) x) x)).symm
  unfold permMonomial
  rw [hsplit]
  have hpath :
      (∏ x ∈ S, A ((pathComplementPerm p τ) x) x) =
        cycleMonomial A p := by
    apply Finset.prod_congr rfl
    intro x hx
    rw [pathComplementPerm_apply_mem p τ]
    simpa [cycleMonomial, S] using hx
  rw [hpath]
  have hcomp :
      (∏ x ∈ Sᶜ, A ((pathComplementPerm p τ) x) x) =
        complementMonomial A p τ := by
    have hsub :
        (∏ x ∈ Sᶜ, A ((pathComplementPerm p τ) x) x) =
          ∏ x : {x : V // x ∈ Sᶜ},
            A ((pathComplementPerm p τ) x) x :=
      Finset.prod_subtype Sᶜ
        (fun x : V => Iff.rfl)
        (fun x : V => A ((pathComplementPerm p τ) x) x)
    have heq :
        (∏ x : {x : V // x ∈ Sᶜ},
          A ((pathComplementPerm p τ) x) x) =
          ∏ x : {x : V // x ∉ p.list},
            (A.submatrix
              (fun y : {x : V // x ∉ p.list} => (y : V))
              (fun y : {x : V // x ∉ p.list} => (y : V))) (τ x) x := by
      apply Fintype.prod_equiv (complementEquiv p)
      intro x
      have hxnot : (x : V) ∉ p.list := (complementEquiv p x).property
      rw [pathComplementPerm_apply_of_not_mem p τ hxnot]
      simp [Matrix.submatrix_apply, complementEquiv]
    calc
      (∏ x ∈ Sᶜ, A ((pathComplementPerm p τ) x) x) =
          ∏ x : {x : V // x ∈ Sᶜ},
            A ((pathComplementPerm p τ) x) x := hsub
      _ =
          ∏ x : {x : V // x ∉ p.list},
            (A.submatrix
              (fun y : {x : V // x ∉ p.list} => (y : V))
              (fun y : {x : V // x ∉ p.list} => (y : V))) (τ x) x := heq
      _ = complementMonomial A p τ := rfl
  rw [hcomp]

theorem permMonomial_eq_path_and_complement
    (A : Matrix V V R) (σ : Equiv.Perm V)
    (hst : s ≠ t) (hts : σ t = s) :
    permMonomial A σ =
      cycleMonomial A (pathOfPerm σ s t hst hts) *
        complementMonomial A (pathOfPerm σ s t hst hts)
          (restrictedPerm σ s t hst hts) := by
  calc
    permMonomial A σ =
        permMonomial A
          (pathComplementPerm (pathOfPerm σ s t hst hts)
            (restrictedPerm σ s t hst hts)) := by
          rw [perm_eq_pathComplement σ s t hst hts]
    _ = cycleMonomial A (pathOfPerm σ s t hst hts) *
        complementMonomial A (pathOfPerm σ s t hst hts)
          (restrictedPerm σ s t hst hts) :=
      permMonomial_pathComplement A
        (pathOfPerm σ s t hst hts)
        (restrictedPerm σ s t hst hts)

end
end TwoDoorsProof
