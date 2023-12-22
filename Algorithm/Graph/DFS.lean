
import Algorithm.Data.Classes.StackLike
import Algorithm.Data.Graph
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic

namespace Graph
variable {V : Type*} [DecidableEq V]
  {EType : Type*} [DecidableEq EType]
  {EColl : Type*} [StackLike EColl EType] [Inhabited EColl]
  {StarList : Type*} [AssocArray StarList V EColl]

def dfs (g : Graph V EType EColl StarList) [Fintype V]
  {BoolArray : Type*} [AssocArray BoolArray V Bool]
  (vs : List V) (visited : BoolArray) : BoolArray :=
  match vs with
  | [] => visited
  | (v :: vs) => if AssocArray.get visited v
    then g.dfs vs visited
    else g.dfs ((StackLike.toList g.star[v]).map g.snd ++ vs) (AssocArray.update visited v true)
termination_by _ => ((Finset.univ.filter (fun v => !(AssocArray.get visited v))).card, vs.length)
decreasing_by
  simp_wf
  first | simp [Prod.lex_iff]; done
        | apply Prod.Lex.left
          apply Finset.card_lt_card
          rw [Finset.ssubset_iff]
          refine ⟨v, by simp, ?_⟩
          rw [Finset.subset_iff]
          simp [*, Function.update]
          intro v
          split_ifs <;> simp

end Graph
