/-
Copyright (c) 2023 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Algorithm.Data.Classes.ToMultiset
import Mathlib.Data.Finset.Card

class ToFinset (C : Type*) (α : outParam Type*) extends Size C α where
  toFinset : C → Finset α
  card_toFinset_eq_size c : (toFinset c).card = size c
export ToFinset (toFinset card_toFinset_eq_size)
attribute [simp] ToFinset.card_toFinset_eq_size

section
variable {α : Type*}

section ToFinset
variable {C α : Type*} [ToFinset C α] (c : C)

instance (priority := 100) : ToMultiset C α where
  toMultiset c := (toFinset c).val
  card_toMultiset_eq_size c := card_toFinset_eq_size c

@[simp]
lemma mem_toFinset (v : α) : v ∈ toFinset c ↔ v ∈ c := .rfl

@[simp]
lemma toFinset_val : (toFinset c).val = toMultiset c := rfl

lemma nodup_toMultiset : (toMultiset c).Nodup := (toFinset c).nodup

variable [DecidableEq α]

end ToFinset
