/-
Copyright (c) 2024 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Algorithm.Data.Classes.AssocArray
import Algorithm.Data.Classes.Bag
import Algorithm.Data.Classes.GetElem

variable {C ι α : Type*}

class Dict.ReadOnly (C : Type*) (ι : outParam Type*) (α : outParam Type*) extends
    Bag.ReadOnly C ι,
    GetElem C ι α (fun c i ↦ i ∈ c)

class Dict (C : Type*) (ι : outParam Type*) (α : outParam Type*) extends
    Bag.ReadOnly C ι,
    EmptyCollection C, LawfulEmptyCollection C ι,
    GetSetEraseElem? C ι α (fun c i ↦ i ∈ c)

section Dict
variable [Dict C ι α]

instance : Dict.ReadOnly C ι α where
instance : Inhabited C where
  default := ∅

def Dict.AssocArray (C : Type*) := C

def Dict.toAssocArray : C ≃ Dict.AssocArray C := Equiv.refl _

instance : Inhabited (Dict.AssocArray C) where
  default := Dict.toAssocArray ∅

instance [Dict C ι α] : AssocArray (Dict.AssocArray C) ι (Option α) none where
  getElem a i _ := (Dict.toAssocArray.symm a)[i]?
  toDFinsupp' a := .mk' ((Dict.toAssocArray.symm a)[·]?)
    (.mk ⟨toMultiset (Dict.toAssocArray.symm a), fun i ↦ by
      simpa [mem_toMultiset, or_iff_not_imp_left] using getElem?_neg _ _ ⟩)
  coe_toDFinsupp'_eq_getElem := by simp
  setElem c i x := Dict.toAssocArray <| alterElem (Dict.toAssocArray.symm c) i (fun _ ↦ x)
  getElem_setElem_self := by simp
  getElem_setElem_of_ne _ _ _ _ hij := by simp [hij]
  getElem_default _ := by simpa [default] using getElem?_neg _ _ (not_mem_empty _)

end Dict
