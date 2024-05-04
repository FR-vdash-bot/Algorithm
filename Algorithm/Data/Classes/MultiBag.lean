/-
Copyright (c) 2023 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Algorithm.Data.Classes.ToMultiset

/-!
See also `LeanColls.MultiBag`.
-/

abbrev DecidableMem (α : Type*) (C : Type*) [Membership α C] :=
  ∀ (a : α) (c : C), Decidable (a ∈ c)

class MultiBag.ReadOnly (C : Type*) (α : outParam Type*) extends
    ToMultiset C α where
  [decidableMem : DecidableMem α C]
  count : α → C → Nat
  count_toMultiset_eq_count : [DecidableEq α] → ∀ a c,
    (toMultiset c).count a = count a c := by intros; rfl
export MultiBag.ReadOnly (count count_toMultiset_eq_count)

class MultiBag (C : Type*) (α : outParam Type*) extends
    MultiBag.ReadOnly C α, EmptyCollection C, Insert α C where
  toMultiset_empty : toMultiset (∅ : C) = 0
export MultiBag (toMultiset_empty)

attribute [instance 100] MultiBag.ReadOnly.decidableMem

section MultiBag.ReadOnly
variable {C α : Type*} [MultiBag.ReadOnly C α] (c : C)

variable [DecidableEq α]

@[simp]
theorem count_eq_zero {a : α} {c : C} : count a c = 0 ↔ a ∉ c :=
  count_toMultiset_eq_count a c ▸ count_toMultiset_eq_zero

theorem count_ne_zero {a : α} {c : C} : count a c ≠ 0 ↔ a ∈ c :=
  count_toMultiset_eq_count a c ▸ count_toMultiset_ne_zero

end MultiBag.ReadOnly
