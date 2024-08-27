/-
Copyright (c) 2023 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
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

lemma get_set_eq (a : Vector α n) (i : Fin n) (v : α) :
    (a.set i v).get i = v := by
  unfold get set
  simp [Array.get_fin_set]

lemma get_set_ne (a : Vector α n) (i : Fin n) (v : α) (j : Fin n) (h : i ≠ j) :
    (a.set i v).get j = a.get j := by
  unfold get set
  simp [Array.get_fin_set, Fin.val_eq_val, h]

@[simp]
lemma get_ofFn (f : Fin n → α) : (ofFn f).get = f := by
  ext; simp [ofFn, get]

end Batteries.Vector

class Get (C : Type*) (ι : outParam Type*) (α : outParam Type*) where
  get : C → ι → α

class GetSet (C : Type*) (ι : outParam Type*) (α : outParam Type*) extends Get C ι α where
  protected set : C → ι → α → C
  get_set_eq a i v : get (set a i v) i = v
  get_set_ne a i v j : i ≠ j → get (set a i v) j = get a j
export GetSet (get_set_eq get_set_ne)

macro:max a:term noWs "[" i:term " => " v:term "]" : term =>
  `(GetSet.set $a $i $v)

macro:max a:term noWs "[" i:term " ↦ " v:term "]" : term =>
  `(GetSet.set $a $i $v)

open Lean PrettyPrinter.Delaborator SubExpr in
/-- Delaborator for `GetSet.set` -/
@[delab app.GetSet.set]
def GetSet.delabSet : Delab := do
  guard <| (← getExpr).isAppOfArity' ``GetSet.set 7
  let a ← withNaryArg 4 delab
  let i ← withNaryArg 5 delab
  let v ← withNaryArg 6 delab
  `($a[$i ↦ $v])

class OfFn (C : Type*) (ι : Type*) (α : Type*) [Get C ι α] (f : ι → α) where
  ofFn : C
  get_ofFn : Get.get ofFn = f
export OfFn (ofFn get_ofFn)

namespace Get

variable {C ι α : Type*}

variable [Get C ι α]

instance : GetElem C ι α fun _ _ ↦ True where
  getElem a i _ := Get.get a i

@[simp]
lemma get_eq_getElem (a : C) (i : ι) : get a i = a[i] := rfl

end Get

namespace GetSet

export Get (get)

end GetSet

section GetSet
open GetSet

variable {C ι α : Type*}

variable [GetSet C ι α]

@[simp]
lemma getElem_set_eq (a : C) (i : ι) (v : α) :
    a[i ↦ v][i] = v :=
  get_set_eq a i v

@[simp]
lemma getElem_set_ne (a : C) (i : ι) (v : α) (j : ι) (h : i ≠ j) :
    a[i ↦ v][j] = a[j] :=
  get_set_ne a i v j h

@[simp]
lemma getElem_set [DecidableEq ι] (a : C) (i : ι) (v : α) (j : ι) :
    a[i ↦ v][j] = if i = j then v else a[j] := by
  split_ifs with h <;> simp [h, getElem_set_eq, getElem_set_ne]

lemma getElem_set_eq_update [DecidableEq ι] (a : C) (i : ι) (v : α) (j : ι) :
    a[i ↦ v][j] = Function.update (get a) i v j := by
  simp [Function.update, eq_comm]

lemma get_set [DecidableEq ι] (a : C) (i : ι) (v : α) (j : ι) :
    get a[i ↦ v] j = if i = j then v else get a j :=
  getElem_set a i v j

lemma get_set_eq_update [DecidableEq ι] (a : C) (i : ι) (v : α) :
    get a[i ↦ v] = Function.update (get a) i v :=
  funext <| getElem_set_eq_update a i v

end GetSet

section OfFn

variable {C ι α : Type*} [Get C ι α] {f : ι → α} [OfFn C ι α f]

@[simp]
lemma getElem_ofFn {i : ι} : (ofFn f : C)[i] = f i :=
  congr_fun get_ofFn i

end OfFn

namespace Batteries.Vector
variable {α : Type*} {n : ℕ} {f : Fin n → α}

instance : GetSet (Vector α n) (Fin n) α where
  set := set
  get := get
  get_set_eq := get_set_eq
  get_set_ne := get_set_ne

instance : OfFn (Vector α n) (Fin n) α f where
  ofFn := ofFn f
  get_ofFn := get_ofFn f

end Batteries.Vector
