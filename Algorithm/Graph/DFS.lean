
import Algorithm.Data.Classes.ToList
import Algorithm.Data.Graph.AdjList
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic

namespace AdjList
variable {V : Type*} [DecidableEq V]
  {EType : Type*} [DecidableEq EType]
  {EColl : Type*} [ToList EColl EType] [Inhabited EColl]
  {StarList : Type*} [AssocArray StarList V EColl]

-- 这个实现中的 vs 大小可能和边的数量级别一样
-- 有什么办法让它既简单，也适合计算？
-- 也许在以后可以改成存迭代器，如果我们有了迭代器类型，不过终止证明会更复杂
-- 如何形式化各种使用 dfs 的算法？如 Tarjan's SCC
def dfs (g : AdjList V EType EColl StarList) [Fintype V]
  {BoolArray : Type*} [AssocArray BoolArray V Bool]
  (vs : List V) (visited : BoolArray) : BoolArray :=
  match vs with
  | [] => visited
  | (v :: vs) => if AssocArray.get visited v
    then g.dfs vs visited
    else g.dfs ((toList g.star[v]).map g.snd ++ vs) (AssocArray.update visited v true)
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

end AdjList
