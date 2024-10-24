/-
Copyright (c) 2023 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Algorithm.Data.Classes.Erase
import Algorithm.Data.Classes.Size
import Mathlib.Data.Multiset.Basic

variable {C α : Type*}

@[mk_iff]
class LawfulEmptyCollection (C : Type*) (α : outParam Type*)
    [Membership α C] [EmptyCollection C] : Prop where
  not_mem_empty (x : α) : x ∉ (∅ : C)
export LawfulEmptyCollection (not_mem_empty)

class ToMultiset (C : Type*) (α : outParam Type*) extends Membership α C, Size C where
  toMultiset : C → Multiset α
  mem c a := a ∈ toMultiset c
  mem_toMultiset {x c} : x ∈ toMultiset c ↔ x ∈ c := by rfl
  size_eq_card_toMultiset c : size c = Multiset.card (toMultiset c)
export ToMultiset (toMultiset mem_toMultiset size_eq_card_toMultiset)

attribute [simp] mem_toMultiset

class ToMultiset.LawfulInsert (C : Type*) (α : outParam Type*)
    [ToMultiset C α] [Insert α C] : Prop where
  toMultiset_insert a (c : C) : toMultiset (insert a c) = a ::ₘ (toMultiset c)
export ToMultiset.LawfulInsert (toMultiset_insert)

attribute [simp] toMultiset_insert

@[mk_iff lawfulErase_iff_toMultiset]
class LawfulErase (C : Type*) (α : outParam Type*)
    [ToMultiset C α] [Erase C α] : Prop where
  toMultiset_erase [DecidableEq α] (c : C) a : toMultiset (erase c a) = (toMultiset c).erase a
export LawfulErase (toMultiset_erase)

attribute [simp] toMultiset_erase

section ToMultiset

instance : ToMultiset (List α) α where
  toMultiset := (↑)
  mem_toMultiset := .rfl
  size_eq_card_toMultiset _ := rfl

instance : ToMultiset (Array α) α where
  toMultiset c := ↑c.toList
  mem_toMultiset := Array.mem_def.symm
  size_eq_card_toMultiset _ := by simp [size]

variable [ToMultiset C α]

section LawfulEmptyCollection
variable [EmptyCollection C]

lemma lawfulEmptyCollection_iff_toMultiset :
    LawfulEmptyCollection C α ↔ toMultiset (∅ : C) = 0 := by
  simp_rw [lawfulEmptyCollection_iff, Multiset.eq_zero_iff_forall_not_mem, mem_toMultiset]

alias ⟨_, LawfulEmptyCollection.of_toMultiset⟩ := lawfulEmptyCollection_iff_toMultiset

@[simp]
lemma toMultiset_empty [LawfulEmptyCollection C α] :
    toMultiset (∅ : C) = 0 := by
  rwa [← lawfulEmptyCollection_iff_toMultiset]

end LawfulEmptyCollection

@[simp]
lemma toMultiset_of_isEmpty {c : C} (h : isEmpty c) : toMultiset c = 0 := by
  simpa [size_eq_card_toMultiset] using h

@[simp]
lemma toMultiset_list (l : List α) : toMultiset l = ↑l := rfl

@[simp]
lemma ToMultiset.not_isEmpty_of_mem {c : C} {x} (hx : x ∈ c) : ¬isEmpty c := by
  simpa [size_eq_card_toMultiset, Multiset.eq_zero_iff_forall_not_mem] using ⟨x, hx⟩

variable [DecidableEq α]

theorem count_toMultiset_eq_zero {a : α} {c : C} : (toMultiset c).count a = 0 ↔ a ∉ c := by
  simp

theorem count_toMultiset_ne_zero {a : α} {c : C} : (toMultiset c).count a ≠ 0 ↔ a ∈ c := by
  simp [count_toMultiset_eq_zero, mem_toMultiset]

class Mergeable (C : Type*) (α : outParam Type*) [ToMultiset C α] where
  merge : C → C → C
  toMultiset_merge s t : toMultiset (merge s t) = toMultiset s + toMultiset t
export Mergeable (merge toMultiset_merge)

attribute [simp] toMultiset_merge

end ToMultiset
