import TwoDoorsProof.PathComplement
import Mathlib.Data.Fintype.Card

namespace TwoDoorsProof

noncomputable section

variable {V : Type*} [DecidableEq V] [Fintype V]
variable {s t : V}

def directedPathCode (p : DirectedPathList s t) :
    Σ n : Fin (Fintype.card V + 1), Fin n → V :=
    ⟨⟨p.list.length,
      Nat.lt_succ_of_le p.nodup.length_le_card⟩,
    fun i => p.list[i.1]'i.2⟩

def directedPathCodeList
    (c : Σ n : Fin (Fintype.card V + 1), Fin n → V) : List V :=
  List.ofFn c.snd

theorem directedPathCode_injective :
    Function.Injective (@directedPathCode V _ s t) := by
  intro p q h
  have hlist : p.list = q.list := by
    calc
      p.list = directedPathCodeList (directedPathCode p) := by
        symm
        exact List.ofFn_getElem
      _ = directedPathCodeList (directedPathCode q) :=
        congrArg directedPathCodeList h
      _ = q.list := List.ofFn_getElem
  have hfirst : p.first = q.first :=
    p.first_is_s.trans q.first_is_s.symm
  have hlast : p.last = q.last :=
    p.last_is_t.trans q.last_is_t.symm
  cases p
  cases q
  simp only [DirectedPathList.mk.injEq]
  exact ⟨hlist, hfirst, hlast⟩

noncomputable instance directedPathListFintype :
    Fintype (DirectedPathList s t) :=
  Fintype.ofInjective (@directedPathCode V _ s t) directedPathCode_injective

end
end TwoDoorsProof
