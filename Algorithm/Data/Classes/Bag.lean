/-
Copyright (c) 2024 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Algorithm.Data.Classes.MultiBag
import Algorithm.Data.Classes.ToFinset

class Bag.ReadOnly (C : Type*) (α : outParam Type*) extends
    ToFinset C α where
  [decidableMem : DecidableMem α C]

class Bag (C : Type*) (α : outParam Type*) extends
    Bag.ReadOnly C α,
    EmptyCollection C, LawfulEmptyCollection C α,
    Insert α C, ToFinset.LawfulInsert C α,
    Erase C α, LawfulErase C α

section Bag.ReadOnly
variable {C α : Type*} [Bag.ReadOnly C α] (c : C)

attribute [local instance] Bag.ReadOnly.decidableMem in
instance : MultiBag.ReadOnly C α where
  count a c := if a ∈ c then 1 else 0
  count_eq_count_toMultiset a c := by
    simp [Multiset.count_eq_of_nodup (nodup_toMultiset c)]

end Bag.ReadOnly
