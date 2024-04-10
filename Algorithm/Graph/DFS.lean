/-
Copyright (c) 2023 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Algorithm.Data.Graph.AdjList
import Algorithm.Data.Graph.IsDFSForest
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic

namespace AdjList
variable {V : Type*} [DecidableEq V]
  {EType : Type*} [DecidableEq EType]
  {EColl : Type*} [ToList EColl EType] [Inhabited EColl]
  {StarList : Type*} [Inhabited StarList] [AssocArray StarList V EColl]

-- 也许在以后可以改成存迭代器
-- 如何形式化各种使用 dfs 的算法？如 Tarjan's SCC

def dfsForest [Fintype V] {BoolArray : Type*} [Inhabited BoolArray] [AssocArray BoolArray V Bool]
    (g : AdjList V EType EColl StarList) (vs : List (Forest V × List V)) (visited : BoolArray) :
    Forest V × BoolArray :=
  match vs with
  | [] => (.nil, default)
  | [(f, [])] => (f, visited)
  | (_, []) :: (_, []) :: _ => (.nil, default)
  | (f, []) :: (fs, v :: vs) :: vss => g.dfsForest ((Forest.node v f fs, vs) :: vss) visited
  | (f, v :: vs) :: vss =>
    if visited[v] then
      g.dfsForest ((f, vs) :: vss) visited
    else
      g.dfsForest ((.nil, g.succList v) :: (f, vs) :: vss) (AssocArray.update visited v true)
termination_by ((toDFinsupp' visited).supportᶜ.card, (vs.map (·.snd.length + 1)).sum)
decreasing_by
  all_goals simp_wf
  · simp [Prod.lex_iff]
    omega
  · simp [Prod.lex_iff]
  · apply Prod.Lex.left
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff]
    refine ⟨v, by simp [*], ?_⟩
    rw [Finset.subset_iff]
    simp [*, Function.update]

def dfs' [Fintype V] {BoolArray : Type*} [Inhabited BoolArray] [AssocArray BoolArray V Bool]
    (g : AdjList V EType EColl StarList) (vs : List (List V)) (visited : BoolArray) :
    BoolArray :=
  match vs with
  | [] => visited
  | [] :: vss => g.dfs' vss visited
  | (v :: vs) :: vss =>
    if visited[v] then
      g.dfs' (vs :: vss) visited
    else
      g.dfs' (g.succList v :: (vs :: vss)) (AssocArray.update visited v true)
termination_by ((toDFinsupp' visited).supportᶜ.card, (vs.map (·.length + 1)).sum)
decreasing_by
  all_goals simp_wf
  · simp [Prod.lex_iff]
  · simp [Prod.lex_iff]
  · apply Prod.Lex.left
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff]
    refine ⟨v, by simp [*], ?_⟩
    rw [Finset.subset_iff]
    simp [*, Function.update]

def dfs [Fintype V] {BoolArray : Type*} [Inhabited BoolArray] [AssocArray BoolArray V Bool]
    (g : AdjList V EType EColl StarList) (vs : List V) (visited : BoolArray) :
    BoolArray :=
  match vs with
  | [] => visited
  | v :: vs =>
    if visited[v] then
      g.dfs vs visited
    else
      g.dfs (g.succList v ++ vs) (AssocArray.update visited v true)
termination_by ((toDFinsupp' visited).supportᶜ.card, vs.length)
decreasing_by
  all_goals simp_wf
  · simp [Prod.lex_iff]
  · apply Prod.Lex.left
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff]
    refine ⟨v, by simp [*], ?_⟩
    rw [Finset.subset_iff]
    simp [*, Function.update]
