/-
Copyright (c) 2023 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/

class Size (C : Type _) (α : outParam <| Type _) where
  size : C → Nat
  isEmpty : C → Bool
  isEmpty_iff_size_eq_zero c : isEmpty c ↔ size c = 0
export Size (size isEmpty isEmpty_iff_size_eq_zero)

attribute [simp] isEmpty_iff_size_eq_zero
