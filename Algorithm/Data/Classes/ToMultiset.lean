/-
Copyright (c) 2023 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Algorithm.Data.Classes.Size
import Mathlib.Data.Multiset.Basic

class ToMultiset (C : Type*) (α : outParam Type*) extends Size C α where
  toMultiset : C → Multiset α
  card_toMultiset_eq_size c : Multiset.card (toMultiset c) = size c
export ToMultiset (toMultiset card_toMultiset_eq_size)

attribute [simp] ToMultiset.card_toMultiset_eq_size

section
variable {α : Type*}

instance : ToMultiset (List α) α where
  toMultiset := (↑)
  size := List.length
  card_toMultiset_eq_size c := rfl
  isEmpty := List.isEmpty
  isEmpty_iff_size_eq_zero l := by cases l <;> simp

instance : ToMultiset (Array α) α where
  toMultiset a := ↑a.toList
  size := Array.size
  card_toMultiset_eq_size c := by simp
  isEmpty := Array.isEmpty
  isEmpty_iff_size_eq_zero l := by simp

section ToMultiset
variable {C α : Type*} [ToMultiset C α] (c : C)

instance (priority := 100) : Membership α C where
  mem a c := a ∈ toMultiset c

@[simp]
lemma mem_toMultiset (v : α) : v ∈ toMultiset c ↔ v ∈ c := .rfl

@[simp]
lemma toMultiset_list (l : List α) : toMultiset l = ↑l := rfl

lemma isEmpty_eq_decide_size : isEmpty c = decide (size c = 0) := by
  simp only [← isEmpty_iff_size_eq_zero, Bool.decide_coe]

lemma isEmpty_eq_size_beq_zero : isEmpty c = (size c == 0) := by
  rw [isEmpty_eq_decide_size]
  cases size c <;> rfl

variable [DecidableEq α]

theorem count_toMultiset_eq_zero {a : α} {c : C} : (toMultiset c).count a = 0 ↔ a ∉ c :=
  Multiset.count_eq_zero

theorem count_toMultiset_ne_zero {a : α} {c : C} : (toMultiset c).count a ≠ 0 ↔ a ∈ c := by
  simp [count_toMultiset_eq_zero]

end ToMultiset
