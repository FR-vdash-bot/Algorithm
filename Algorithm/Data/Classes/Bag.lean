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
export MultiBag.ReadOnly (count count_toMultiset_eq_count)

section Bag.ReadOnly
variable {C α : Type*} [Bag.ReadOnly C α] (c : C)

attribute [local instance 100] Bag.ReadOnly.decidableMem in
instance : MultiBag.ReadOnly C α where
  count a c := if a ∈ c then 1 else 0
  count_toMultiset_eq_count a c := by convert Multiset.count_eq_of_nodup (nodup_toMultiset c)

instance : AssocArray.ReadOnly C α Bool where
  get c a := a ∈ c
  toDFinsupp' c := ⟨(· ∈ c), Trunc.mk ⟨toMultiset c, fun i ↦ by simpa using em _⟩⟩
  coe_toDFinsupp'_eq_get a := rfl

end Bag.ReadOnly
