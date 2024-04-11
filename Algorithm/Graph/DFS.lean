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
  {StarList : Type*} [AssocArray.ReadOnly StarList V EColl]

-- 也许在以后可以改成存迭代器
-- 如何形式化各种使用 dfs 的算法？如 Tarjan's SCC

def dfsForest' [Fintype V] {BoolArray : Type*} [Inhabited BoolArray] [AssocArray BoolArray V Bool]
    (g : AdjList V EType EColl StarList) (vs : List V) (visited : BoolArray) :
    Forest V × { b : BoolArray // (toDFinsupp' visited).support ⊆ (toDFinsupp' b).support } :=
  match vs with
  | [] => (.nil, ⟨visited, le_rfl⟩)
  | v :: vs =>
    if visited[v] then
      g.dfsForest' vs visited
    else
      have h : (toDFinsupp' visited).support ⊆
          (toDFinsupp' (AssocArray.update visited v true)).support := by
        simp [DFinsupp'.support_update_ne]
      let (fc, ⟨vis₁, hvis₁⟩) := g.dfsForest' (g.succList v) (AssocArray.update visited v true)
      let (fs, ⟨vis₂, hvis₂⟩) := g.dfsForest' vs vis₁
      (Forest.node v fc fs, ⟨vis₂, (h.trans hvis₁).trans hvis₂⟩)
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
  · have : (toDFinsupp' vis₁).supportᶜ.card ≤ (toDFinsupp' visited).supportᶜ.card := by
      apply Finset.card_le_card
      simpa using h.trans hvis₁
    simpa [Prod.lex_iff, ← le_iff_lt_or_eq]

lemma roots_dfsForest'_fst_subset [Fintype V] {BoolArray : Type*} [Inhabited BoolArray]
    [AssocArray BoolArray V Bool] (g : AdjList V EType EColl StarList)
    (vs : List V) (visited : BoolArray) :
    (g.dfsForest' vs visited).1.roots ⊆ {v | v ∈ vs} := by
  match vs with
  | [] => unfold dfsForest'; exact Set.empty_subset _
  | v :: vs =>
    unfold dfsForest'; split
    · intro _ h
      simpa using .inr (g.roots_dfsForest'_fst_subset vs visited h)
    dsimp
    rintro _ (rfl | h)
    · simp
    · simp only [List.mem_cons]
      exact .inr <| g.roots_dfsForest'_fst_subset vs _ h

lemma subset_support_toDFinsupp'_dfsForest'_snd [Fintype V] {BoolArray : Type*}
    [Inhabited BoolArray] [AssocArray BoolArray V Bool] (g : AdjList V EType EColl StarList)
    (vs : List V) (visited : BoolArray) :
    {v | v ∈ vs} ⊆ (toDFinsupp' (g.dfsForest' vs visited).2.val).support := by
  match vs with
  | [] => simp
  | v :: vs =>
    simp only [List.mem_cons]
    unfold dfsForest'; split
    · rintro _ (rfl | h)
      · apply (g.dfsForest' vs visited).2.prop
        simpa
      · exact g.subset_support_toDFinsupp'_dfsForest'_snd vs visited h
    · dsimp
      rintro _ (rfl | h)
      · apply (g.dfsForest' _ _).2.prop
        apply (g.dfsForest' _ _).2.prop
        simp
      · exact g.subset_support_toDFinsupp'_dfsForest'_snd vs _ h

lemma isDFSForest_dfsForest' [Fintype V] {BoolArray : Type*} [Inhabited BoolArray]
    [AssocArray BoolArray V Bool] (g : AdjList V EType EColl StarList)
    (vs : List V) (visited : BoolArray) :
    g.IsDFSForest
      (toDFinsupp' visited).support
      (toDFinsupp' (g.dfsForest' vs visited).2.val).support
      (g.dfsForest' vs visited).1 := by
  match vs with
  | [] => unfold dfsForest'; constructor
  | v :: vs =>
    unfold dfsForest'; split; · exact isDFSForest_dfsForest' _ _ _
    rename_i v vs hv
    let rc := g.dfsForest' (g.succList v) (AssocArray.update visited v true)
    dsimp; apply IsDFSForest.node (toDFinsupp' rc.2.val).support
    · simp [hv]
    · convert isDFSForest_dfsForest' _ _ _
      simp [DFinsupp'.support_update_ne]
    · exact g.succList_eq_succSet _ ▸ (g.roots_dfsForest'_fst_subset _ _)
    · exact g.succList_eq_succSet _ ▸ (g.subset_support_toDFinsupp'_dfsForest'_snd _ _)
    · exact g.isDFSForest_dfsForest' _ _
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
  · have h : (toDFinsupp' visited).support ⊆
        (toDFinsupp' (AssocArray.update visited v true)).support := by
      simp [DFinsupp'.support_update_ne]
    have : (toDFinsupp' rc.2.val).supportᶜ.card ≤ (toDFinsupp' visited).supportᶜ.card := by
      apply Finset.card_le_card
      simpa using h.trans rc.2.prop
    simpa [Prod.lex_iff, ← le_iff_lt_or_eq]

def dfsForest [Fintype V] {BoolArray : Type*} [Inhabited BoolArray] [AssocArray BoolArray V Bool]
    (g : AdjList V EType EColl StarList) (vs : List V) (visited : BoolArray) :
    Forest V × BoolArray :=
  (g.dfsForest' vs visited).map id Subtype.val

lemma dfsForest_spec [Fintype V] {BoolArray : Type*} [Inhabited BoolArray]
    [AssocArray BoolArray V Bool] (g : AdjList V EType EColl StarList) (vs : List V) :
    let (f, vis) := (g.dfsForest vs (default : BoolArray))
    f.support = (toDFinsupp' vis).support ∧ ∀ v, v ∈ f.support ↔ ∃ r ∈ vs, g.Reachable r v := by
  have := g.isDFSForest_dfsForest' vs (default : BoolArray)
  simp only [AssocArray.toDFinsupp'_default, DFinsupp'.support_default, Finset.coe_empty] at this
  dsimp
  refine ⟨this.spec.1, fun v ↦ ⟨fun hv ↦ ?_, fun ⟨r, hr, hrv⟩ ↦ this.complete v r ?_ hrv⟩⟩
  · obtain ⟨r, hr, hrv⟩ := this.sound v hv
    exact ⟨r, g.roots_dfsForest'_fst_subset vs _ hr, hrv⟩
  · exact this.spec.1 ▸ g.subset_support_toDFinsupp'_dfsForest'_snd vs default hr

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
