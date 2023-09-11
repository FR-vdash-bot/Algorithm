/-
Copyright (c) 2023 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Mathlib.Data.List.Basic

class Collection (C : Type*) (α : outParam Type*) where
  size : C → Nat
  empty : C
  isEmpty : C → Bool
  isEmpty_empty : isEmpty empty
  size_eq_zero_iff c : size c = 0 ↔ isEmpty c

section
variable {α : Type*}

instance : Collection (List α) α where
  size := List.length
  empty := []
  isEmpty := List.isEmpty
  isEmpty_empty := rfl
  size_eq_zero_iff l := by cases l <;> (simp; rfl)

instance : Collection (Array α) α where
  size := Array.size
  empty := #[]
  isEmpty := Array.isEmpty
  isEmpty_empty := rfl
  size_eq_zero_iff l := by simp

end

namespace Collection
variable {C α : Type*} [Collection C α] (c : C)

lemma isEmpty_eq_decide_size : isEmpty c = decide (size c = 0) := by
  simp only [size_eq_zero_iff, Bool.decide_coe]

lemma isEmpty_eq_size_beq_zero : isEmpty c = (size c == 0) := by
  rw [isEmpty_eq_decide_size]
  cases size c <;> rfl

end Collection
