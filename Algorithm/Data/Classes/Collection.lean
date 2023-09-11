/-
Copyright (c) 2023 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Mathlib.Data.Multiset.Basic

class Collection (C : Type*) (α : outParam Type*) where
  empty : C
  toMultiset : C → Multiset α
  isEmpty : C → Bool
  size : C → Nat
  card_toMultiset_eq_size c : Multiset.card (toMultiset c) = size c
  toMultiset_empty : toMultiset empty = 0
  isEmpty_iff_size_eq_zero c : isEmpty c ↔ size c = 0

attribute [simp] Collection.card_toMultiset_eq_size

section
variable {α : Type*}

instance : Collection (List α) α where
  empty := []
  toMultiset := (↑)
  size := List.length
  card_toMultiset_eq_size c := rfl
  isEmpty := List.isEmpty
  toMultiset_empty := rfl
  isEmpty_iff_size_eq_zero l := by cases l <;> (simp; rfl)

instance : Collection (Array α) α where
  empty := #[]
  toMultiset a := ↑a.toListRev
  size := Array.size
  card_toMultiset_eq_size c := by simp
  isEmpty := Array.isEmpty
  toMultiset_empty := rfl
  isEmpty_iff_size_eq_zero l := by simp

namespace Collection
variable {C α : Type*} [Collection C α] (c : C)

instance (priority := 100) : Membership α C where
  mem a c := a ∈ toMultiset c

lemma isEmpty_empty : isEmpty (empty : C) := by
  rw [isEmpty_iff_size_eq_zero, ← card_toMultiset_eq_size, toMultiset_empty]
  rfl

lemma isEmpty_eq_decide_size : isEmpty c = decide (size c = 0) := by
  simp only [← isEmpty_iff_size_eq_zero, Bool.decide_coe]

lemma isEmpty_eq_size_beq_zero : isEmpty c = (size c == 0) := by
  rw [isEmpty_eq_decide_size]
  cases size c <;> rfl

end Collection
