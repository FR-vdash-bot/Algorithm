/-
Copyright (c) 2023 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Algorithm.Data.Classes.ToMultiset

class Container (C : Type*) (α : outParam Type*) extends ToMultiset C α where
  empty : C
  toMultiset_empty : toMultiset empty = 0
export Container (toMultiset_empty)

section
variable {α : Type*}

instance : Container (List α) α where
  empty := []
  toMultiset_empty := rfl

instance : Container (Array α) α where
  empty := #[]
  toMultiset_empty := rfl

section Container
variable {C α : Type*} [Container C α] (c : C)

instance (priority := 100) : Membership α C where
  mem a c := a ∈ toMultiset c

def mkEmpty (C) {α} [Container C α]  : C := Container.empty

@[simp]
lemma toMultiset_mkEmpty : toMultiset (mkEmpty C) = 0 := Container.toMultiset_empty

lemma isEmpty_mkEmpty : isEmpty (mkEmpty C) := by
  rw [isEmpty_iff_size_eq_zero, ← card_toMultiset_eq_size, toMultiset_mkEmpty]
  rfl

end Container
