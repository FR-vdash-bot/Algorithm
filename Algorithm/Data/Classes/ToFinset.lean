/-
Copyright (c) 2023 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Algorithm.Data.Classes.ToMultiset
import Mathlib.Data.Finset.Card

class ToFinset (C : Type*) (α : outParam Type*) extends Size C α where
  toFinset : C → Finset α
  size_eq_card_toFinset c : size c = (toFinset c).card
export ToFinset (toFinset size_eq_card_toFinset)

attribute [simp] size_eq_card_toFinset

-- Actually the same as `ToMultiset` version
class ToFinset.LawfulEmptyCollection (C : Type*) (α : outParam Type*)
    [ToFinset C α] [EmptyCollection C] : Prop where
  toFinset_empty : toFinset (∅ : C) = ∅
export ToFinset.LawfulEmptyCollection (toFinset_empty)

attribute [simp] toFinset_empty

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
variable [EmptyCollection C] [ToFinset.LawfulEmptyCollection C α] (c : C)

instance : ToMultiset.LawfulEmptyCollection C α where
  toMultiset_empty := congr_arg Finset.val toFinset_empty

end LawfulEmptyCollection

lemma ToFinset.mem_iff (v : α) : v ∈ c ↔ v ∈ toFinset c := .rfl

lemma mem_toFinset (v : α) : v ∈ toFinset c ↔ v ∈ c := .rfl

@[simp]
lemma toFinset_val : (toFinset c).val = toMultiset c := rfl

lemma nodup_toMultiset : (toMultiset c).Nodup := (toFinset c).nodup

variable [DecidableEq α]

end ToFinset
