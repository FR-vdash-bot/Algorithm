/-
Copyright (c) 2023 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Algorithm.Data.Classes.Size
import Mathlib.Data.Multiset.Basic

class ToMultiset (C : Type*) (α : outParam Type*) extends Size C where
  toMultiset : C → Multiset α
  size_eq_card_toMultiset c : size c = Multiset.card (toMultiset c)
export ToMultiset (toMultiset size_eq_card_toMultiset)

@[mk_iff ToMultiset.lawfulEmptyCollection_iff]
class LawfulEmptyCollection (C : Type*) (α : outParam Type*)
    [ToMultiset C α] [EmptyCollection C] : Prop where
  toMultiset_empty : toMultiset (∅ : C) = 0
export LawfulEmptyCollection (toMultiset_empty)

attribute [simp] toMultiset_empty

class ToMultiset.LawfulInsert (C : Type*) (α : outParam Type*)
    [ToMultiset C α] [Insert α C] : Prop where
  toMultiset_insert a (c : C) : toMultiset (insert a c) = a ::ₘ (toMultiset c)
export ToMultiset.LawfulInsert (toMultiset_insert)

attribute [simp] toMultiset_insert

section
variable {α : Type*}

instance : ToMultiset (List α) α where
  toMultiset := (↑)
  size_eq_card_toMultiset _ := rfl

instance : ToMultiset (Array α) α where
  toMultiset c := ↑c.toList
  size_eq_card_toMultiset _ := by simp [size]

section ToMultiset
variable {C α : Type*} [ToMultiset C α] (c : C)

instance (priority := 100) : Membership α C where
  mem c a := a ∈ toMultiset c

lemma ToMultiset.mem_iff {c : C} {v : α} : v ∈ c ↔ v ∈ toMultiset c := .rfl

lemma mem_toMultiset {c : C} {v : α} : v ∈ toMultiset c ↔ v ∈ c := .rfl

@[simp]
lemma toMultiset_of_isEmpty (h : isEmpty c) : toMultiset c = 0 := by
  simpa [size_eq_card_toMultiset] using h

@[simp]
lemma toMultiset_list (l : List α) : toMultiset l = ↑l := rfl

@[simp]
lemma ToMultiset.not_isEmpty_of_mem {c : C} {v} (hv : v ∈ c) : ¬isEmpty c := by
  simpa [size_eq_card_toMultiset, Multiset.eq_zero_iff_forall_not_mem] using ⟨v, hv⟩

variable [DecidableEq α]

theorem count_toMultiset_eq_zero {a : α} {c : C} : (toMultiset c).count a = 0 ↔ a ∉ c :=
  Multiset.count_eq_zero

theorem count_toMultiset_ne_zero {a : α} {c : C} : (toMultiset c).count a ≠ 0 ↔ a ∈ c := by
  simp [count_toMultiset_eq_zero, mem_toMultiset]

class Mergeable (C : Type*) (α : outParam Type*) [ToMultiset C α] where
  merge : C → C → C
  toMultiset_merge s t : toMultiset (merge s t) = toMultiset s + toMultiset t
export Mergeable (merge toMultiset_merge)

attribute [simp] toMultiset_merge

end ToMultiset
