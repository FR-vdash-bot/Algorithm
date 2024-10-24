/-
Copyright (c) 2024 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Algorithm.Data.Classes.Dict

namespace Std.HashMap
variable {ι α : Type*} [BEq ι] [Hashable ι]

instance : Size (HashMap ι α) where
  size := size
  isEmpty := isEmpty
  isEmpty_iff_size_eq_zero := Nat.beq_eq.to_iff

instance : LawfulEmptyCollection (HashMap ι α) ι where
  not_mem_empty _ := not_mem_empty

lemma distinct_keys [EquivBEq ι] [LawfulHashable ι] (c : HashMap ι α) :
    c.keys.Pairwise (fun a b => (a == b) = false) := by
  sorry

@[simp]
lemma mem_keys [EquivBEq ι] [LawfulHashable ι] (c : HashMap ι α) {i : ι} :
    i ∈ c.keys ↔ i ∈ c := by
  sorry

@[simp]
lemma length_keys [EquivBEq ι] [LawfulHashable ι] (c : HashMap ι α) :
    c.keys.length = c.size := by
  sorry

variable [LawfulBEq ι]

instance : ToFinset (HashMap ι α) ι where
  toFinset c := ⟨c.keys, by simpa [List.Nodup] using distinct_keys c⟩
  mem_toFinset := by simp
  size_eq_card_toFinset := by simp [Size.size]

instance : Dict (HashMap ι α) ι α where
  setElem := insert
  valid_setElem := by simp
  getElem_setElem_self := by simp
  getElem_setElem_of_ne _ _ _ _ hij := by simp [getElem_insert, hij]
  erase := erase
  valid_erase := by simp
  getElem_erase_of_ne := by simp

end Std.HashMap
