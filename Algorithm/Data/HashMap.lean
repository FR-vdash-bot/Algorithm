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
  isEmpty_iff_size_eq_zero := beq_iff_eq

instance : LawfulEmptyCollection (HashMap ι α) ι where
  not_mem_empty _ := not_mem_empty

variable [LawfulBEq ι]

instance : ToFinset (HashMap ι α) ι where
  toFinset c := ⟨c.keys, by simpa [List.Nodup] using c.distinct_keys⟩
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
