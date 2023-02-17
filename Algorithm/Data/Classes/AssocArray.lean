/-
Copyright (c) 2023 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Mathlib.Data.Fin.Basic
import Std.Data.Array.Lemmas

/-- `AssocArray ι α M` is a data structure that acts like a finitely supported function `ι → α`
  with single point update operation. -/
class AssocArray (ι : outParam <| Type _) [DecidableEq ι]
    (α : outParam <| Type _) [Inhabited α] (M : Type _) where
  empty : M
  set : M → ι → α → M
  get : M → ι → α
  get_set : get (set a i v) = Function.update (get a) i v
  get_empty : get empty = Function.const _ default

attribute [simp] AssocArray.get_set AssocArray.get_empty

namespace Array

lemma get_fin_set (a : Array α) (i : Fin a.size) (v : α) (j : Fin (set a i v).size) :
    (a.set i v).get j = if i.1 = j.1 then v else a[j.1] := by
  rw [get_eq_getElem, get_set]

instance [Inhabited α] : AssocArray (Fin n) α {a : Array α // a.size = n} where
  empty := ⟨.mk <| List.replicate n default, List.length_replicate _ _⟩
  set a i v := ⟨a.1.set (Fin.cast a.2.symm i) v, (Array.size_set _ _ _).trans a.2⟩
  get a i := a.1.get (Fin.cast a.2.symm i)
  get_set {a i v} := by
    simp_rw [get_fin_set]; simp [Function.update, Fin.val_eq_val, eq_comm (a := i)]
  get_empty := by
    ext; simp [get]

end Array

namespace AssocArray
variable {ι : Type _} [DecidableEq ι] {α : Type _} [Inhabited α] {M : Type _} [AssocArray ι α M]

-- instance instGetElem : GetElem M ι α (fun _ _ ↦ True) := ⟨fun m i _ ↦ AssocArray.get m i⟩

end AssocArray
