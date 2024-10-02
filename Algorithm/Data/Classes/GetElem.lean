/-
Copyright (c) 2023 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Algorithm.Tactic.Attr.Register
import Batteries.Data.Vector.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Logic.Function.Basic

universe u v

namespace Array
variable {α : Type*} {n : ℕ}

lemma get_fin_set (a : Array α) (i : Fin a.size) (v : α) (j : Fin (set a i v).size) :
    (a.set i v).get j = if i.1 = j.1 then v else a[j.1] := by
  rw [get_eq_getElem, get_set]

end Array

namespace Batteries

namespace Vector
variable {α : Type*} {n : ℕ}

lemma get_set_self (a : Vector α n) (i : Fin n) (v : α) :
    (a.set i v).get i = v := by
  unfold get set
  simp [Array.get_fin_set]

lemma get_set_of_ne (a : Vector α n) {i : Fin n} (v : α) {j : Fin n} (h : i ≠ j) :
    (a.set i v).get j = a.get j := by
  unfold get set
  simp [Array.get_fin_set, Fin.val_eq_val, h]

@[simp]
lemma get_ofFn (f : Fin n → α) : (ofFn f).get = f := by
  ext; simp [ofFn, get]

@[simp]
lemma getElem_ofFn (f : Fin n → α) (i : Fin n) : (ofFn f)[i] = f i := by
  change (ofFn f).get i = f i
  simp

end Batteries.Vector

class SetElem (C : Type*) (ι : Type*) (α : outParam Type*) where
  protected setElem : C → ι → α → C

macro:max a:term noWs "[" i:term " => " v:term "]" : term => `(SetElem.setElem $a $i $v)
macro:max a:term noWs "[" i:term " ↦ " v:term "]" : term => `(SetElem.setElem $a $i $v)

open Lean PrettyPrinter.Delaborator SubExpr in
/-- Delaborator for `SetElem.setElem` -/
@[app_delab SetElem.setElem]
def SetElem.delabSetElem : Delab := do
  guard <| (← getExpr).isAppOfArity' ``SetElem.setElem 7
  let a ← withNaryArg 4 delab
  let i ← withNaryArg 5 delab
  let v ← withNaryArg 6 delab
  `($a[$i ↦ $v])

class EraseElem (C : Type*) (ι : Type*) (α : outParam Type*) where
  protected eraseElem : C → ι → C

macro:max a:term noWs "[" i:term " => " "-" "]" : term => `(EraseElem.eraseElem $a $i)
macro:max a:term noWs "[" i:term " ↦ " "-" "]" : term => `(EraseElem.eraseElem $a $i)

open Lean PrettyPrinter.Delaborator SubExpr in
/-- Delaborator for `EraseElem.eraseElem` -/
@[app_delab EraseElem.eraseElem]
def EraseElem.delabEraseElem : Delab := do
  guard <| (← getExpr).isAppOfArity' ``EraseElem.eraseElem 6
  let a ← withNaryArg 4 delab
  let i ← withNaryArg 5 delab
  `($a[$i ↦ -])

class GetSetElem (C : Type*) (ι : Type*) (α : outParam Type*)
    (Valid : outParam (C → ι → Prop)) extends GetElem C ι α Valid, SetElem C ι α where
  valid_setElem_self {a i} v :
    Valid a[i ↦ v] i := by get_elem_tactic
  valid_setElem_of_valid {a} (i : ι) v {j} :
    Valid a j → Valid a[i ↦ v] j := by get_elem_tactic
  valid_of_valid_setElem {a i} v {j} :
    i ≠ j → Valid a[i ↦ v] j → Valid a j := by get_elem_tactic
  getElem_setElem_self c i v :
    c[i ↦ v][i]'(valid_setElem_self v) = v
  getElem_setElem_of_ne c {i} v {j} (hij : i ≠ j)
    (hs : Valid c[i ↦ v] j := by get_elem_tactic) (h : Valid c j := by get_elem_tactic) :
    c[i ↦ v][j]'hs = c[j]'h
export GetSetElem (valid_setElem_self valid_setElem_of_valid valid_of_valid_setElem
  getElem_setElem_self getElem_setElem_of_ne)

attribute [get_elem_simps] valid_setElem_self valid_setElem_of_valid valid_of_valid_setElem
attribute [simp] getElem_setElem_self getElem_setElem_of_ne

macro_rules | `(tactic| get_elem_tactic_trivial) => `(tactic| simp [get_elem_simps, *]; done)

class OfFn (C : Type*) (ι : Type*) (α : Type*) (Valid : C → ι → Prop) [GetElem C ι α Valid]
    (f : ι → α) where
  ofFn : C
  valid_ofFn i : Valid ofFn i := by get_elem_tactic
  getElem_ofFn i (h := valid_ofFn i) : ofFn[i]'h = f i
export OfFn (ofFn valid_ofFn getElem_ofFn)

class AllValid {C : Type*} {ι : Type*} (Valid : C → ι → Prop) : Prop where
  all_valid (a i) : Valid a i := by get_elem_tactic
export AllValid (all_valid)

attribute [simp] all_valid

instance {C ι : Type*} : AllValid (C := C) (ι := ι) (fun _ _ ↦ True) where

section GetSetElem
open GetSetElem

variable {C ι α : Type*} {Valid : C → ι → Prop}

variable [GetSetElem C ι α Valid]

@[simp]
lemma getElem_setElem [DecidableEq ι] (a : C) (i : ι) (v : α) (j : ι) (hj : Valid a j) :
    a[i ↦ v][j] = if i = j then v else a[j] := by
  split_ifs with h <;> simp [h, hj]

variable [AllValid Valid]

lemma getElem_setElem_eq_update [DecidableEq ι] (a : C) (i : ι) (v : α) (j : ι) :
    a[i ↦ v][j] = Function.update (a[·]) i v j := by
  simp [Function.update, eq_comm]

end GetSetElem

namespace Batteries.Vector
variable {α : Type*} {n : ℕ} {f : Fin n → α}

-- We had to write `fun _ (i : Fin n) ↦ (i : Nat) < n`, see `Fin.instGetElemFinVal`
instance : GetSetElem (Vector α n) (Fin n) α (fun _ i ↦ i < n) where
  getElem a i _ := a.get i
  setElem := set
  getElem_setElem_self a i v := a.get_set_self i v
  getElem_setElem_of_ne a _ v _ hij _ _ := a.get_set_of_ne v hij

instance : OfFn (Vector α n) (Fin n) α (fun _ i ↦ i < n) f where
  ofFn := ofFn f
  getElem_ofFn i _ := getElem_ofFn f i

instance : AllValid (C := Vector α n) (ι := Fin n) (fun _ i ↦ i < n) where

end Batteries.Vector
