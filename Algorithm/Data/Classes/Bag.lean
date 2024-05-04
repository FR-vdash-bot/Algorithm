/-
Copyright (c) 2024 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Algorithm.Data.Classes.AssocArray
import Algorithm.Data.Classes.MultiBag
import Algorithm.Data.Classes.ToFinset

/-!
See also `LeanColls.Bag`.
-/

class Bag.ReadOnly (C : Type*) (α : outParam Type*) extends
    ToFinset C α where
  [decidableMem : DecidableMem α C]

class Bag.LawfulEmptyCollection (C : Type*) (α : outParam Type*)
    [Bag.ReadOnly C α] [EmptyCollection C] : Prop where
  toFinset_empty : toFinset (∅ : C) = ∅
export Bag.LawfulEmptyCollection (toFinset_empty)

class Bag (C : Type*) (α : outParam Type*) [EmptyCollection C] extends
    Bag.ReadOnly C α, Bag.LawfulEmptyCollection C α, Insert α C where
  toFinset_insert a c : [DecidableEq α] → toFinset (insert a c) = Insert.insert a (toFinset c)
export Bag (toFinset_insert)

section Bag.ReadOnly
variable {C α : Type*} [Bag.ReadOnly C α] (c : C)

attribute [local instance] Bag.ReadOnly.decidableMem in
instance : MultiBag.ReadOnly C α where
  count a c := if a ∈ c then 1 else 0
  count_eq_count_toMultiset a c := by symm; convert Multiset.count_eq_of_nodup (nodup_toMultiset c)

instance : AssocArray.ReadOnly C α Bool where
  get c a := a ∈ c
  toDFinsupp' c := ⟨(· ∈ c), Trunc.mk ⟨toMultiset c, fun i ↦ by simpa using em _⟩⟩
  coe_toDFinsupp'_eq_get a := rfl

section Bag.LawfulEmptyCollection
variable [EmptyCollection C] [Bag.LawfulEmptyCollection C α] (c : C)

instance : MultiBag.LawfulEmptyCollection C α where
  toMultiset_empty := congr_arg Finset.val toFinset_empty

end Bag.LawfulEmptyCollection

end Bag.ReadOnly
