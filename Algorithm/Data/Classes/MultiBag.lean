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
  count_eq_count_toMultiset : [DecidableEq α] → ∀ a c,
    count a c = (toMultiset c).count a := by intros; rfl
export MultiBag.ReadOnly (count count_eq_count_toMultiset)

class MultiBag.LawfulEmptyCollection (C : Type*) (α : outParam Type*)
    [MultiBag.ReadOnly C α] [EmptyCollection C] : Prop where
  toMultiset_empty : toMultiset (∅ : C) = 0
export MultiBag.LawfulEmptyCollection (toMultiset_empty)

class MultiBag (C : Type*) (α : outParam Type*) [EmptyCollection C] extends
    MultiBag.ReadOnly C α, MultiBag.LawfulEmptyCollection C α, Insert α C where
  toMultiset_insert a c : toMultiset (insert a c) = a ::ₘ (toMultiset c)
export MultiBag (toMultiset_insert)

attribute [instance 100] MultiBag.ReadOnly.decidableMem

attribute [simp] count_eq_count_toMultiset toMultiset_empty toMultiset_insert

section MultiBag.ReadOnly
variable {C α : Type*} [MultiBag.ReadOnly C α] (c : C)

variable [DecidableEq α]

theorem count_eq_zero {a : α} {c : C} : count a c = 0 ↔ a ∉ c :=
  count_eq_count_toMultiset a c ▸ count_toMultiset_eq_zero

theorem count_ne_zero {a : α} {c : C} : count a c ≠ 0 ↔ a ∈ c :=
  count_eq_count_toMultiset a c ▸ count_toMultiset_ne_zero

end MultiBag.ReadOnly
