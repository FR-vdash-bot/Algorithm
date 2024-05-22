/-
Copyright (c) 2023 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Algorithm.Data.Classes.ToMultiset
import Mathlib.Data.Finset.Card

class ToFinset (C : Type*) (α : outParam Type*) extends Size C where
  toFinset : C → Finset α
  size_eq_card_toFinset c : size c = (toFinset c).card
export ToFinset (toFinset size_eq_card_toFinset)

class ToFinset.LawfulInsert (C : Type*) (α : outParam Type*)
    [ToFinset C α] [Insert α C] : Prop where
  toFinset_insert a (c : C) : [DecidableEq α] → toFinset (insert a c) = Insert.insert a (toFinset c)
export ToFinset.LawfulInsert (toFinset_insert)

attribute [simp] toFinset_insert

section
variable {α : Type*}

section ToFinset
variable {C α : Type*} [ToFinset C α] (c : C)

instance (priority := 100) ToFinset.toMultiset : ToMultiset C α where
  toMultiset c := (toFinset c).val
  size_eq_card_toMultiset c := size_eq_card_toFinset c

section LawfulEmptyCollection
variable [EmptyCollection C] [LawfulEmptyCollection C α]

lemma ToFinset.lawfulEmptyCollection_iff [ToFinset C α] [EmptyCollection C] :
    LawfulEmptyCollection C α ↔ toFinset (∅ : C) = ∅ := by
  rw [ToMultiset.lawfulEmptyCollection_iff]
  change (toFinset (∅ : C)).val = ∅ ↔ _
  simp

alias ⟨_, LawfulEmptyCollection.ofToFinset⟩ := ToFinset.lawfulEmptyCollection_iff

@[simp]
lemma toFinset_empty [ToFinset C α] [EmptyCollection C] [inst : LawfulEmptyCollection C α] :
    toFinset (∅ : C) = ∅ := by
  rwa [ToFinset.lawfulEmptyCollection_iff] at inst

end LawfulEmptyCollection

lemma ToFinset.mem_iff {c : C} {v : α} : v ∈ c ↔ v ∈ toFinset c := .rfl

lemma mem_toFinset {c : C} {v : α} : v ∈ toFinset c ↔ v ∈ c := .rfl

@[simp]
lemma toFinset_val : (toFinset c).val = toMultiset c := rfl

lemma nodup_toMultiset : (toMultiset c).Nodup := (toFinset c).nodup

variable [DecidableEq α]

end ToFinset
