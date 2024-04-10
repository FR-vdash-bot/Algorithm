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

def dfsForest' [Fintype V] {BoolArray : Type*} [Inhabited BoolArray] [AssocArray BoolArray V Bool]
    (g : AdjList V EType EColl StarList) (vs : List V) (fs : Forest V) (visited : BoolArray) :
    Forest V × { b : BoolArray // (toDFinsupp' b).supportᶜ.card ≤ (toDFinsupp' visited).supportᶜ.card } :=
  match vs with
  | [] => (fs, ⟨visited, le_rfl⟩)
  | v :: vs =>
    if visited[v] then
      g.dfsForest' vs fs visited
    else
      have h : (toDFinsupp' (AssocArray.update visited v true)).supportᶜ.card ≤
          (toDFinsupp' visited).supportᶜ.card := by
        apply Finset.card_le_card
        simpa [DFinsupp'.support_update_ne] using Finset.erase_subset _ _
      let (f₁, ⟨vis₁, hvis₁⟩) := g.dfsForest' (g.succList v) .nil (AssocArray.update visited v true)
      let (f₂, ⟨vis₂, hvis₂⟩) := g.dfsForest' vs (Forest.node v f₁ fs) vis₁
      (f₂, ⟨vis₂, hvis₂.trans (hvis₁.trans h)⟩)
termination_by ((toDFinsupp' visited).supportᶜ.card, vs)
decreasing_by
  all_goals simp_wf
  · simp [Prod.lex_iff]
  · apply Prod.Lex.left
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff]
    refine ⟨v, by simp [*], ?_⟩
    rw [Finset.subset_iff]
    simp [*, Function.update]
  · simpa [Prod.lex_iff, ← le_iff_lt_or_eq] using hvis₁.trans h

def dfsForest [Fintype V] {BoolArray : Type*} [Inhabited BoolArray] [AssocArray BoolArray V Bool]
    (g : AdjList V EType EColl StarList) (vs : List V) (fs : Forest V) (visited : BoolArray) :
    Forest V × BoolArray :=
  (g.dfsForest' vs fs visited).map id Subtype.val

def dfsForestTR [Fintype V] {BoolArray : Type*} [Inhabited BoolArray] [AssocArray BoolArray V Bool]
    (g : AdjList V EType EColl StarList) (vs : List (Forest V × List V)) (visited : BoolArray) :
    Forest V × BoolArray :=
  match vs with
  | [] => (.nil, default)
  | [(f, [])] => (f, visited)
  | (_, []) :: (_, []) :: _ => (.nil, default)
  | (f, []) :: (fs, v :: vs) :: vss => g.dfsForestTR ((Forest.node v f fs, vs) :: vss) visited
  | (f, v :: vs) :: vss =>
    if visited[v] then
      g.dfsForestTR ((f, vs) :: vss) visited
    else
      g.dfsForestTR ((.nil, g.succList v) :: (f, vs) :: vss) (AssocArray.update visited v true)
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

def dfs'TR [Fintype V] {BoolArray : Type*} [Inhabited BoolArray] [AssocArray BoolArray V Bool]
    (g : AdjList V EType EColl StarList) (vs : List (List V)) (visited : BoolArray) :
    BoolArray :=
  match vs with
  | [] => visited
  | [] :: vss => g.dfs'TR vss visited
  | (v :: vs) :: vss =>
    if visited[v] then
      g.dfs'TR (vs :: vss) visited
    else
      g.dfs'TR (g.succList v :: (vs :: vss)) (AssocArray.update visited v true)
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

def dfsTR [Fintype V] {BoolArray : Type*} [Inhabited BoolArray] [AssocArray BoolArray V Bool]
    (g : AdjList V EType EColl StarList) (vs : List V) (visited : BoolArray) :
    BoolArray :=
  match vs with
  | [] => visited
  | v :: vs =>
    if visited[v] then
      g.dfsTR vs visited
    else
      g.dfsTR (g.succList v ++ vs) (AssocArray.update visited v true)
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
