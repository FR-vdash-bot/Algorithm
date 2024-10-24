/-
Copyright (c) 2023 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Batteries.Data.Array.Lemmas
import Batteries.Data.List.Lemmas

variable {C α : Type _}

class Size (C : Type _) where
  size : C → Nat
  isEmpty : C → Bool
  isEmpty_iff_size_eq_zero {c} : isEmpty c ↔ size c = 0
export Size (size isEmpty isEmpty_iff_size_eq_zero)

attribute [simp] isEmpty_iff_size_eq_zero

instance : Size (List α) where
  size := List.length
  isEmpty := List.isEmpty
  isEmpty_iff_size_eq_zero := by simp

instance : Size (Array α) where
  size := Array.size
  isEmpty := Array.isEmpty
  isEmpty_iff_size_eq_zero := by simp

variable [Size C] (c : C)

theorem isEmpty_eq_decide_size : isEmpty c = decide (size c = 0) := by
  simp only [← isEmpty_iff_size_eq_zero, Bool.decide_coe]

theorem isEmpty_eq_size_beq_zero : isEmpty c = (size c == 0) := by
  rw [isEmpty_eq_decide_size]
  cases size c <;> rfl
