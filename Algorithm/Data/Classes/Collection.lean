/-
Copyright (c) 2023 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Mathlib.Data.Multiset.Basic

class CollectionCore (C : Type*) (α : outParam Type*) where
  size : C → Nat
  isEmpty : C → Bool
  isEmpty_iff_size_eq_zero c : isEmpty c ↔ size c = 0
export CollectionCore (size isEmpty isEmpty_iff_size_eq_zero)

-- do not need to write `toMultiset` if we have `toList`
class Collection (C : Type*) (α : outParam Type*) extends CollectionCore C α where
  toMultiset : C → Multiset α
  card_toMultiset_eq_size c : Multiset.card (toMultiset c) = size c
export Collection (toMultiset card_toMultiset_eq_size)

attribute [simp] Collection.card_toMultiset_eq_size

section
variable {α : Type*}

instance : Collection (List α) α where
  toMultiset := (↑)
  size := List.length
  card_toMultiset_eq_size c := rfl
  isEmpty := List.isEmpty
  isEmpty_iff_size_eq_zero l := by cases l <;> simp

instance : Collection (Array α) α where
  toMultiset a := ↑a.toList
  size := Array.size
  card_toMultiset_eq_size c := by simp
  isEmpty := Array.isEmpty
  isEmpty_iff_size_eq_zero l := by simp

section Collection
variable {C α : Type*} [Collection C α] (c : C)

instance (priority := 100) : Membership α C where
  mem a c := a ∈ toMultiset c

@[simp]
lemma mem_toMultiset (v : α) : v ∈ toMultiset c ↔ v ∈ c := .rfl

lemma isEmpty_eq_decide_size : isEmpty c = decide (size c = 0) := by
  simp only [← isEmpty_iff_size_eq_zero, Bool.decide_coe]

lemma isEmpty_eq_size_beq_zero : isEmpty c = (size c == 0) := by
  rw [isEmpty_eq_decide_size]
  cases size c <;> rfl

variable [DecidableEq α]

def countSlow (a : α) (c : C) : Nat :=
  (Collection.toMultiset c).count a

@[simp]
theorem countSlow_eq_zero {a : α} {c : C} : countSlow a c = 0 ↔ a ∉ c :=
  Multiset.count_eq_zero

theorem countSlow_ne_zero {a : α} {c : C} : countSlow a c ≠ 0 ↔ a ∈ c := by
  simp [Ne.def, countSlow_eq_zero]

class Count (C : Type*) (α : outParam Type*) [Collection C α] where
  count : [DecidableEq α] → α → C → Nat
  count_eq_countSlow : [DecidableEq α] → ∀ a c,
    count a c = countSlow a c := by intros; rfl
export Count (count count_eq_countSlow)

end Collection
