/-
Copyright (c) 2023 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Algorithm.Tactic.Attr.Register
import Algorithm.Data.Classes.Erase
import Batteries.Data.Vector.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Logic.Function.Basic

variable {C ι α : Type*} {Valid : C → ι → Prop}

namespace Array
variable {α : Type*} {n : ℕ}

lemma get_fin_set (c : Array α) (i : Fin c.size) (v : α) (j : Fin (set c i v).size) :
    (c.set i v).get j = if i.1 = j.1 then v else c[j.1] := by
  rw [get_eq_getElem, get_set]

end Array

namespace Batteries

namespace Vector
variable {α : Type*} {n : ℕ}

lemma get_set_self (c : Vector α n) (i : Fin n) (v : α) :
    (c.set i v).get i = v := by
  unfold get set
  simp [Array.get_fin_set]

lemma get_set_of_ne (c : Vector α n) {i : Fin n} (v : α) {j : Fin n} (h : i ≠ j) :
    (c.set i v).get j = c.get j := by
  unfold get set
  simp [Array.get_fin_set, Fin.val_eq_val, h]

@[simp]
lemma get_ofFn (f : Fin n → α) : (ofFn f).get = f := by
  ext; simp [ofFn, get]

lemma getElem_ofFn (f : Fin n → α) (i : Fin n) : (ofFn f)[i] = f i := by
  change (ofFn f).get i = f i
  simp

end Batteries.Vector

macro_rules | `(tactic| get_elem_tactic_trivial) => `(tactic| simp_all [getElem_simps]; done)

class SetElem (C : Type*) (ι : Type*) (α : outParam Type*) where
  protected setElem : C → ι → α → C

macro:max c:term noWs "[" i:term " => " v:term "]" : term => `(SetElem.setElem $c $i $v)
macro:max c:term noWs "[" i:term " ↦ " v:term "]" : term => `(SetElem.setElem $c $i $v)

open Lean PrettyPrinter.Delaborator SubExpr in
/-- Delaborator for `SetElem.setElem` -/
@[app_delab SetElem.setElem]
def SetElem.delabSetElem : Delab := do
  guard <| (← getExpr).isAppOfArity' ``SetElem.setElem 7
  let c ← withNaryArg 4 delab
  let i ← withNaryArg 5 delab
  let v ← withNaryArg 6 delab
  `($c[$i ↦ $v])

class GetSetElem (C : Type*) (ι : Type*) (α : outParam Type*)
    (Valid : outParam (C → ι → Prop)) extends GetElem C ι α Valid, SetElem C ι α where
  valid_setElem {c} {i : ι} {x j} : Valid c[i ↦ x] j ↔ i = j ∨ Valid c j := by get_elem_tactic
  getElem_setElem_self c i x :
    c[i ↦ x][i]'(valid_setElem.mpr <| .inl rfl) = x
  getElem_setElem_of_ne c {i} x {j} (hij : i ≠ j)
    (hs : Valid c[i ↦ x] j := by get_elem_tactic) (h : Valid c j := by get_elem_tactic) :
    c[i ↦ x][j]'hs = c[j]'h
export GetSetElem (valid_setElem getElem_setElem_self getElem_setElem_of_ne)

attribute [getElem_simps] valid_setElem
attribute [simp] getElem_setElem_self getElem_setElem_of_ne

lemma valid_setElem_self [GetSetElem C ι α Valid] {c : C} {i : ι} {x} :
    Valid c[i ↦ x] i := by
  get_elem_tactic

lemma valid_setElem_of_ne [GetSetElem C ι α Valid] {c : C} {i : ι} x {j : ι} :
    i ≠ j → (Valid c[i ↦ x] j ↔ Valid c j) := by
  get_elem_tactic

lemma valid_of_valid_setElem [GetSetElem C ι α Valid] {c : C} {i : ι} x {j : ι} :
    i ≠ j → Valid c[i ↦ x] j → Valid c j := by
  get_elem_tactic

lemma valid_setElem_of_valid [GetSetElem C ι α Valid] {c : C} (i : ι) x {j} :
    Valid c j → Valid c[i ↦ x] j := by
  get_elem_tactic

-- TODO: should be a field of a typeclass
def modifyElem [GetSetElem C ι α Valid] (c i) [dec : Decidable (Valid c i)] (f : α → α) : C :=
  match dec with
  | .isFalse _ => c
  | .isTrue _ => c[i ↦ f c[i]]

class GetSetEraseElem (C : Type*) (ι : Type*) (α : outParam Type*)
    (Valid : outParam (C → ι → Prop)) extends GetSetElem C ι α Valid, Erase C ι where
  valid_erase {c i j} : Valid (erase c i) j ↔ i ≠ j ∧ Valid c j := by get_elem_tactic
  getElem_erase_of_ne c {i j} (hij : i ≠ j)
    (hs : Valid (erase c i) j := by get_elem_tactic) (h : Valid c j := by get_elem_tactic) :
    (erase c i)[j]'hs = c[j]'h
export GetSetEraseElem (valid_erase getElem_erase_of_ne)

attribute [getElem_simps] valid_erase
attribute [simp] getElem_erase_of_ne

lemma not_valid_erase_self [GetSetEraseElem C ι α Valid] {c : C} {i : ι} :
    ¬Valid (erase c i) i := by
  get_elem_tactic

lemma valid_erase_of_ne [GetSetEraseElem C ι α Valid] {c : C} {i j : ι} :
    i ≠ j → (Valid (erase c i) j ↔ Valid c j) := by
  get_elem_tactic

lemma valid_of_valid_erase [GetSetEraseElem C ι α Valid] {c : C} {i j : ι} :
    Valid (erase c i) j → Valid c j := by
  get_elem_tactic

lemma valid_erase_of_valid [GetSetEraseElem C ι α Valid] {c : C} {i j : ι} :
    i ≠ j → Valid c j → Valid (erase c i) j := by
  get_elem_tactic

class GetSetEraseElem? (C : Type*) (ι : Type*) (α : outParam Type*)
    (Valid : outParam (C → ι → Prop)) extends
    GetElem? C ι α Valid, GetSetEraseElem C ι α Valid, LawfulGetElem C ι α Valid where

section GetSetEraseElem?
variable [GetSetEraseElem? C ι α Valid]

@[simp]
lemma getElem?_setElem_self (c : C) (i : ι) (x : α) :
    c[i ↦ x][i]? = x := by
  classical rw [getElem?_pos, getElem_setElem_self] -- TODO: lean4#5812

@[simp]
lemma getElem?_setElem_of_ne (c : C) {i : ι} (x : α) {j : ι} (hij : i ≠ j) :
    c[i ↦ x][j]? = c[j]? := by
  classical rw [getElem?_def, getElem?_def]
  split_ifs with h <;> get_elem_tactic

@[simp]
lemma getElem?_erase_self (c : C) (i : ι) :
    (erase c i)[i]? = none := by
  classical exact getElem?_neg _ i not_valid_erase_self -- TODO: lean4#5812

@[simp]
lemma getElem?_erase_of_ne (c : C) {i j : ι} (hij : i ≠ j) :
    (erase c i)[j]? = c[j]? := by
  classical rw [getElem?_def, getElem?_def]
  split_ifs with h <;> get_elem_tactic

-- TODO: should be a field of a typeclass
def alterElem (c : C) (i : ι) (f : Option α → Option α) : C :=
  match f c[i]? with
  | none => erase c i
  | some x => c[i ↦ x]

@[simp]
lemma getElem?_alterElem_self (c : C) (i : ι) (f : Option α → Option α) :
    (alterElem c i f)[i]? = f c[i]? := by
  rw [alterElem]
  split
  · simp [*]
  · classical simp [getElem?_pos _ _ valid_setElem_self, *] -- TODO: lean4#5812

@[simp]
lemma getElem?_alterElem_of_ne (c : C) {i : ι} (f : Option α → Option α) {j : ι} (hij : i ≠ j) :
    (alterElem c i f)[j]? = c[j]? := by
  rw [alterElem]
  split
  · simp [*]
  · rw [getElem?_setElem_of_ne c _ hij]

end GetSetEraseElem?

class HasValid (C : Type*) (ι : Type*) where
  Valid : C → ι → Prop

class GetElemAllValid (C : Type*) (ι : Type*) (α : outParam Type*) extends
    HasValid C ι, GetElem C ι α Valid where
  Valid := fun _ _ ↦ True
  all_valid {c i} : Valid c i := by get_elem_tactic
export GetElemAllValid (all_valid)

attribute [simp] all_valid

macro_rules | `(tactic| get_elem_tactic_trivial) => `(tactic| exact GetElemAllValid.all_valid)

class GetSetElemAllValid (C : Type*) (ι : Type*) (α : outParam Type*) extends
    GetElemAllValid C ι α, SetElem C ι α where
  getElem_setElem_self (c : C) (i : ι) v : c[i ↦ v][i] = v
  getElem_setElem_of_ne (c : C) {i : ι} v {j} (hij : i ≠ j) : c[i ↦ v][j] = c[j]

instance GetSetElemAllValid.toGetSetElem (C ι α : Type*) [GetSetElemAllValid C ι α] :
    GetSetElem C ι α HasValid.Valid where
  getElem_setElem_self := getElem_setElem_self
  getElem_setElem_of_ne _ _ _ _ hij _ _ := getElem_setElem_of_ne _ _ hij

section GetSetElem
variable [GetSetElem C ι α Valid]

@[simp, nolint simpNF] -- It sometimes does work, see `getElem_setElem'`.
lemma getElem_setElem [DecidableEq ι] (c : C) (i : ι) (v : α) (j : ι)
    (hj : Valid c j := by get_elem_tactic) :
    c[i ↦ v][j] = if i = j then v else c[j] := by
  split_ifs with h <;> simp [h, hj]

end GetSetElem

section GetSetElemAllValid
variable [GetSetElemAllValid C ι α]

lemma getElem_setElem' [DecidableEq ι] (c : C) (i : ι) (v : α) (j : ι) :
    c[i ↦ v][j] = if i = j then v else c[j] := by
  simp

lemma getElem_setElem_eq_update [DecidableEq ι] (c : C) (i : ι) (v : α) (j : ι) :
    c[i ↦ v][j] = Function.update (c[·]) i v j := by
  simp [Function.update, eq_comm]

class OfFn (C : Type*) (ι : Type*) (α : Type*) [GetElemAllValid C ι α] (f : ι → α) where
  ofFn : C
  getElem_ofFn i : ofFn[i] = f i
export OfFn (ofFn getElem_ofFn)

attribute [simp] getElem_ofFn

end GetSetElemAllValid

namespace Batteries.Vector
variable {α : Type*} {n : ℕ} {f : Fin n → α}

instance instGetSetElemAllValid : GetSetElemAllValid (Vector α n) (Fin n) α where
  Valid _ i := (i : ℕ) < n -- `Fin.instGetElemFinVal`
  getElem c i _ := c.get i
  setElem := set
  getElem_setElem_self c i v := c.get_set_self i v
  getElem_setElem_of_ne c _ v _ hij := c.get_set_of_ne v hij

instance : OfFn (Vector α n) (Fin n) α f where
  ofFn := ofFn f
  getElem_ofFn := getElem_ofFn f

example : (instGetSetElemAllValid (α := α) (n := n)).toGetElem = Fin.instGetElemFinVal := rfl

end Batteries.Vector
