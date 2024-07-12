/-
Copyright (c) 2023 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Algorithm.Data.DFinsupp'.Defs
import Batteries.Data.Array.Lemmas
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Setoid.Basic

universe u v

namespace Array
variable {α : Type*} {n : ℕ}

lemma get_fin_set (a : Array α) (i : Fin a.size) (v : α) (j : Fin (set a i v).size) :
    (a.set i v).get j = if i.1 = j.1 then v else a[j.1] := by
  rw [get_eq_getElem, get_set]

end Array

namespace Batteries793

structure Vector (α : Type u) (n : Nat) where
  toArray : Array α
  size_eq : toArray.size = n
deriving Repr, BEq, DecidableEq

namespace Vector
variable {α : Type*} {n : ℕ}

def ofFn (f : Fin n → α) : Vector α n :=
  ⟨.ofFn f, Array.size_ofFn f⟩

def get (a : Vector α n) (i : Fin n) : α :=
  a.1.get (i.cast a.2.symm)

def set (a : Vector α n) (i : Fin n) (v : α) : Vector α n :=
  ⟨a.1.set (i.cast a.2.symm) v, (Array.size_set _ _ _).trans a.2⟩

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

set_option linter.unusedVariables false in -- TODO: generalize
@[nolint unusedArguments]
protected abbrev WithDefault (α : Type u) (n : Nat) (f : Fin n → α) := Vector α n

instance {α n f} : Inhabited (Vector.WithDefault α n f) where
  default := .ofFn f

@[simp]
lemma get_default {f} : (default : Vector.WithDefault α n f).get = f :=
  get_ofFn _

end Batteries793.Vector

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

class AssocDArray.ReadOnly (C : Type*) (ι : outParam Type*)
    (α : outParam Type*) (d : outParam <| ι → α) extends Get C ι α where
  toDFinsupp' : C → Π₀' i, [α, d i]
  coe_toDFinsupp'_eq_get : ∀ a : C, ⇑(toDFinsupp' a) = get a
export AssocDArray.ReadOnly (toDFinsupp' coe_toDFinsupp'_eq_get)

/-- `AssocDArray C ι α d` is a data structure that acts like a finitely supported function
  `Π₀' i, [α, d i]` with single point update operation. -/
class AssocDArray (C : Type*) [Inhabited C] (ι : outParam Type*)
    (α : outParam Type*) (d : outParam <| ι → α)
    extends AssocDArray.ReadOnly C ι α d, GetSet C ι α where
  get_default : get default = d

abbrev AssocArray.ReadOnly (C : Type*) (ι : outParam Type*)
    (α : outParam Type*) (d : outParam α) :=
  AssocDArray.ReadOnly C ι α (fun _ ↦ d)

/-- `AssocArray C ι α d` is a data structure that acts like a finitely supported function
  `ι →₀' [α, d]` with single point update operation. -/
abbrev AssocArray (C : Type*) [Inhabited C] (ι : outParam Type*)
    (α : outParam Type*) (d : outParam α) :=
  AssocDArray C ι α (fun _ ↦ d)

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

attribute [simp] AssocDArray.get_default coe_toDFinsupp'_eq_get

section AssocDArray

variable {C ι α : Type*} {d : ι → α}

variable [Inhabited C] [AssocDArray C ι α d]

instance : OfFn C ι α d where
  ofFn := default
  get_ofFn := AssocDArray.get_default

lemma toDFinsupp'_apply_eq_getElem (a : C) (i : ι) : toDFinsupp' a i = a[i] := by simp

@[simp]
lemma AssocDArray.getElem_default (i : ι) :
    (default : C)[i] = d i :=
  congr_fun AssocDArray.get_default i

@[simp]
lemma toDFinsupp'_set [DecidableEq ι] (a : C) (i : ι) (v : α) :
    toDFinsupp' a[i ↦ v] = (toDFinsupp' a).update i v := by
  ext; simp [getElem_set_eq_update, -getElem_set]

@[simp]
lemma toDFinsupp'_default :
    toDFinsupp' (default : C) = default := by
  ext; simp

end AssocDArray

namespace Batteries793.Vector
variable {α : Type*} {n : ℕ} {f : Fin n → α}

instance : AssocDArray (Vector.WithDefault α n f) (Fin n) α f where
  set := set
  get := get
  get_set_eq := get_set_eq
  get_set_ne := get_set_ne
  get_default := get_default
  toDFinsupp' a := DFinsupp'.equivFunOnFintype.symm (get a)
  coe_toDFinsupp'_eq_get _ := DFinsupp'.coe_equivFunOnFintype_symm _

end Batteries793.Vector

namespace AssocArray

export Get (get)
export AssocDArray (get_default)

class Ext (C : Type*) [Inhabited C] (ι : outParam Type*)
    (α : outParam Type*) (d : outParam α) [AssocArray C ι α d] : Prop where
  ext : ∀ {m₁ m₂ : C}, get m₁ = get m₂ → m₁ = m₂

variable {C : Type*} [Inhabited C] {ι : Type*} {α : Type*} {d : α} [AssocArray C ι α d]

variable (C)

protected def Quotient := @Quotient C (Setoid.ker get)

instance : Inhabited (AssocArray.Quotient C) :=
  inferInstanceAs <| Inhabited (@Quotient C (Setoid.ker get))

instance : AssocArray (AssocArray.Quotient C) ι α d where
  set q i v := q.map' (·[i ↦ v]) (by classical exact
    fun _ _ hm ↦ (Eq.congr (get_set_eq_update _ _ _) (get_set_eq_update _ _ _)).mpr (by rw [hm]))
  get := Quotient.lift get (fun _ _ ↦ id)
  get_set_eq q i v := q.inductionOn (get_set_eq · _ _)
  get_set_ne q i v j h := q.inductionOn (get_set_ne · _ _ _ h)
  get_default := get_default
  toDFinsupp' := Quotient.lift toDFinsupp' (fun _ _ ↦ by
    simpa only [DFunLike.ext'_iff, coe_toDFinsupp'_eq_get] using id)
  coe_toDFinsupp'_eq_get a := by
    induction a using Quotient.ind
    exact coe_toDFinsupp'_eq_get _

instance : Ext (AssocArray.Quotient C) ι α d where
  ext {m₁ m₂} := m₂.inductionOn <| m₁.inductionOn (fun _ _ ha ↦ Quotient.sound ha)
export Ext (ext)

def listIndicator (l : List ι) (f : ∀ i ∈ l, α) : C :=
  match l with
  | [] => default
  | (i :: l) => (listIndicator l (fun i hi ↦ f i (List.mem_cons_of_mem _ hi)))[i ↦
    (f i (List.mem_cons_self _ _))]

variable {C}

lemma get_listIndicator [DecidableEq ι] (l : List ι) (f : ∀ i ∈ l, α) :
    get (listIndicator C l f) = (fun i ↦ if hi : i ∈ l then f i hi else d) :=
  match l with
  | [] => by ext; simp [listIndicator, get_default, Function.const]
  | (i :: l) => by
    ext j
    rw [listIndicator, get_set_eq_update, Function.update_apply]
    split_ifs with h₁ h₂ h₂
    · simp [h₁]
    · simp [h₁] at h₂
    · simp_rw [get_listIndicator, dif_pos (List.mem_of_ne_of_mem h₁ h₂)]
    · simp_rw [get_listIndicator, dif_neg (List.not_mem_of_not_mem_cons h₂)]

variable [Ext C ι α d]
variable (C)

def indicator (s : Finset ι) (f : ∀ i ∈ s, α) : C :=
  let this := Equiv.subtypeQuotientEquivQuotientSubtype (fun l : List ι ↦ ↑l = s.1)
    (fun m ↦ m = s.1) (fun i ↦ Iff.rfl) (fun _ _ ↦ Iff.rfl) ⟨s.1, rfl⟩
  this.liftOn (fun l ↦ listIndicator C l (fun i hi ↦ f i (l.2 ▸ hi : i ∈ s.1)))
    (fun l₁ l₂ hl ↦ ext <| by classical simp_rw [get_listIndicator, List.Perm.mem_iff hl])

variable {C}

lemma get_indicator [DecidableEq ι] (s : Finset ι) (f : ∀ i ∈ s, α) :
    get (indicator C s f) = (fun i ↦ if hi : i ∈ s then f i hi else d) := by
  unfold indicator
  change _ = (fun i ↦ if hi : i ∈ s.1 then _ else _)
  obtain ⟨l, hl⟩ := s.1.exists_rep
  simp_rw [← hl]
  rw [Equiv.subtypeQuotientEquivQuotientSubtype_mk]
  dsimp
  rw [get_listIndicator]
  rfl

abbrev toOfFn [Fintype ι] (f : ι → α) : OfFn C ι α f where
  ofFn := indicator C Finset.univ (fun i _ ↦ f i)
  get_ofFn := by
    convert (get_indicator _ _).trans <| funext fun _ ↦ dif_pos <| Finset.mem_univ _
    classical infer_instance

end AssocArray

class HasDefaultAssocDArray (ι : Type u) (α : Type v) (f : ι → α)
    (DefaultAssocDArray : outParam <| Type max u v) [Inhabited DefaultAssocDArray] where
  [assocDArray : AssocDArray DefaultAssocDArray ι α f]

@[nolint unusedArguments]
def DefaultAssocDArray (ι : Type u) (α : Type v) (f : ι → α) {D : Type _} [Inhabited D]
    [HasDefaultAssocDArray ι α f D] :=
  D

instance {n α f} : HasDefaultAssocDArray (Fin n) α f (Batteries793.Vector.WithDefault α n f) where

example {n α f} := DefaultAssocDArray (Fin n) α f
