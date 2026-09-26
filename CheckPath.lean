import TwoDoorsProof.PathComplement
import Mathlib.Data.Fintype.Card
namespace TwoDoorsProof
noncomputable section
variable {V : Type*} [DecidableEq V] [Fintype V]
variable {s t : V}
def bar (p : DirectedPathList s t) :
    Σ n : Fin (Fintype.card V + 1), Fin n → V :=
  ⟨⟨p.list.length, Nat.lt_succ_of_le p.nodup.length_le_card⟩,
    fun i => p.list[i.1]'i.2⟩
#check bar
#check @bar
#check DirectedPathList.ext
#check DirectedPathList.mk.injEq
#check Sigma.ext_iff
#check Sigma.ext
#check List.ext_getElem?
#check proof_irrelheq
#check Subsingleton.elim
#check eq_of_heq
#check HEq.to_eq
#check List.heq
#check List.ext
#check Fin.cast
#check Fin.cast_heq
#check Fin.ext
#check congrArg
#check HEq
#check HEq.fun_congr
#check HEq.congr_fun
#check congr_fun
#check cast
#check Eq.ndrec
#check Eq.rec
#check Fin.cast
#check Fin.cast_eq_cast
#check List.ofFn
#check List.ofFn_getElem
#check List.getElem_ofFn
#check List.ofFn_getElem?
#check List.ofFn_eq_map
#check List.ofFn_length
#check heq_of_eq
#check HEq.rfl
#check HEq.trans
#check HEq.symm
#check eqRec_heq
#check cast_heq
#check eq_mp_heq
#check Sigma.ext
#check Equiv.cast
#check Equiv.cast_apply
#check Equiv.cast_eq_iff_heq
#check Equiv.coe_cast
#check heq_fun
#check HEq.fun_iff
#check heq_fun_iff
#check HEq.funLike_iff
#check Equiv.heq_iff
#check Equiv.ext_iff
#check DFunLike.heq_fun
end
end TwoDoorsProof
