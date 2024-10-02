/-
Copyright (c) 2023 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Algorithm.Data.Classes.GetElem
import Algorithm.Data.DFinsupp'.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Setoid.Basic

universe u v

namespace Batteries

namespace Vector
variable {α : Type*} {n : ℕ}

set_option linter.unusedVariables false in -- TODO: generalize
@[nolint unusedArguments]
protected abbrev WithDefault (α : Type u) (n : Nat) (f : Fin n → α) := Vector α n

instance {α n f} : Inhabited (Vector.WithDefault α n f) where
  default := .ofFn f

@[simp]
lemma get_default {f} : (default : Vector.WithDefault α n f).get = f :=
  get_ofFn _

end Batteries.Vector

class AssocDArray.ReadOnly (C : Type*) (ι : outParam Type*)
    (α : outParam Type*) (V : outParam _) (d : outParam <| ι → α) extends
    GetElem C ι α V, AllValid V where
  toDFinsupp' : C → Π₀' i, [α, d i]
  coe_toDFinsupp'_eq_getElem : ∀ a, ⇑(toDFinsupp' a) = (a[·])
export AssocDArray.ReadOnly (toDFinsupp' coe_toDFinsupp'_eq_getElem)

/-- `AssocDArray C ι α d` is a data structure that acts like a finitely supported function
  `Π₀' i, [α, d i]` with single point update operation. -/
class AssocDArray (C : Type*) [Inhabited C] (ι : outParam Type*)
    (α : outParam Type*) (V : outParam _) (d : outParam <| ι → α) extends
    AssocDArray.ReadOnly C ι α V d, GetSetElem C ι α V, AllValid V where
  getElem_default i : (default : C)[i] = d i

abbrev AssocArray.ReadOnly (C : Type*) (ι : outParam Type*)
    (α : outParam Type*) (V : outParam _) (d : outParam α) :=
  AssocDArray.ReadOnly C ι α V (fun _ ↦ d)

/-- `AssocArray C ι α d` is a data structure that acts like a finitely supported function
  `ι →₀' [α, d]` with single point update operation. -/
abbrev AssocArray (C : Type*) [Inhabited C] (ι : outParam Type*)
    (α : outParam Type*) (V : outParam _) (d : outParam α) :=
  AssocDArray C ι α V (fun _ ↦ d)

attribute [simp] AssocDArray.getElem_default coe_toDFinsupp'_eq_getElem

section AssocDArray

variable {C ι α : Type*} {V} {d : ι → α}

variable [Inhabited C] [AssocDArray C ι α V d]

instance : OfFn C ι α V d where
  ofFn := default
  getElem_ofFn i _ := AssocDArray.getElem_default i

lemma toDFinsupp'_apply_eq_getElem (a : C) (i : ι) : toDFinsupp' a i = a[i] := by simp

@[simp]
lemma toDFinsupp'_setElem [DecidableEq ι] (a : C) (i : ι) (v : α) :
    toDFinsupp' a[i ↦ v] = (toDFinsupp' a).update i v := by
  ext; simp [getElem_setElem_eq_update, - getElem_setElem]

@[simp]
lemma toDFinsupp'_default :
    toDFinsupp' (default : C) = default := by
  ext; simp

end AssocDArray

namespace Batteries.Vector.WithDefault
variable {α : Type*} {n : ℕ} {f : Fin n → α}

instance instAssocDArray :
    AssocDArray (Vector.WithDefault α n f) (Fin n) α (fun _ i ↦ i < n) f where
  getElem a i _ := a.get i
  setElem := set
  getElem_setElem_self a i v := a.get_set_self i v
  getElem_setElem_of_ne a _ v _ hij _ _ := a.get_set_of_ne v hij
  getElem_default i := congrFun get_default i
  toDFinsupp' a := DFinsupp'.equivFunOnFintype.symm (get a)
  coe_toDFinsupp'_eq_getElem _ := DFinsupp'.coe_equivFunOnFintype_symm _

end Batteries.Vector.WithDefault

namespace AssocArray

export AssocDArray (getElem_default)

class Ext (C : Type*) [Inhabited C] (ι : outParam Type*)
    (α : outParam Type*) (V : outParam _) (d : outParam α) [AssocArray C ι α V d] : Prop where
  ext : ∀ {m₁ m₂ : C}, (∀ i : ι, m₁[i] = m₂[i]) → m₁ = m₂

variable {C : Type*} [Inhabited C] {ι : Type*} {α : Type*} {V} {d : α}
  [AssocArray C ι α V d] [AllValid V]

variable (C)

protected def Quotient := @Quotient C (Setoid.ker (fun (a : C) (i : ι) ↦ a[i]))

instance : Inhabited (AssocArray.Quotient C) :=
  inferInstanceAs <| Inhabited (@Quotient C (Setoid.ker _))

instance : AssocArray (AssocArray.Quotient C) ι α (fun _ _ ↦ True) d where
  getElem c i _ := Quotient.lift (·[·] : C → ι → α) (fun _ _ ↦ id) c i
  setElem q i v := q.map' (·[i ↦ v]) fun _ _ hm ↦ funext fun j ↦ by
    classical simp [congrFun hm j]
  getElem_setElem_self q i v := q.inductionOn (getElem_setElem_self · i v)
  getElem_setElem_of_ne q i v j h := q.inductionOn (fun _ _ ↦ getElem_setElem_of_ne · v h)
  getElem_default := getElem_default
  toDFinsupp' := Quotient.lift toDFinsupp' (fun _ _ ↦ by
    simpa only [DFunLike.ext'_iff, coe_toDFinsupp'_eq_getElem] using id)
  coe_toDFinsupp'_eq_getElem a := by
    induction a using Quotient.ind
    exact coe_toDFinsupp'_eq_getElem _

instance : Ext (AssocArray.Quotient C) ι α (fun _ _ ↦ True) d where
  ext {m₁ m₂} := m₂.inductionOn <| m₁.inductionOn (fun _ _ ha ↦ Quotient.sound <| funext ha)
export Ext (ext)

def listIndicator (l : List ι) (f : ∀ i ∈ l, α) : C :=
  match l with
  | [] => default
  | (i :: l) => (listIndicator l (fun i hi ↦ f i (List.mem_cons_of_mem _ hi)))[i ↦
    (f i (List.mem_cons_self _ _))]

variable {C}

lemma getElem_listIndicator [DecidableEq ι] (l : List ι) (f : ∀ i ∈ l, α) (i) :
    (listIndicator C l f)[i] = if hi : i ∈ l then f i hi else d :=
  match l with
  | [] => by simp [listIndicator, getElem_default, Function.const]
  | _ :: l => by
    rw [listIndicator, getElem_setElem_eq_update, Function.update_apply]
    split_ifs with h₁ h₂ h₂
    · simp [h₁]
    · simp [h₁] at h₂
    · simp_rw [getElem_listIndicator, dif_pos (List.mem_of_ne_of_mem h₁ h₂)]
    · simp_rw [getElem_listIndicator, dif_neg (List.not_mem_of_not_mem_cons h₂)]

variable [Ext C ι α V d]
variable (C)

def indicator (s : Finset ι) (f : ∀ i ∈ s, α) : C :=
  let this := Equiv.subtypeQuotientEquivQuotientSubtype (fun l : List ι ↦ ↑l = s.1)
    (fun m ↦ m = s.1) (fun i ↦ Iff.rfl) (fun _ _ ↦ Iff.rfl) ⟨s.1, rfl⟩
  this.liftOn (fun l ↦ listIndicator C l (fun i hi ↦ f i (l.2 ▸ hi : i ∈ s.1)))
    (fun l₁ l₂ hl ↦ ext <| by classical simp [getElem_listIndicator, List.Perm.mem_iff hl])

variable {C}

lemma getElem_indicator [DecidableEq ι] (s : Finset ι) (f : ∀ i ∈ s, α) (i) :
    (indicator C s f)[i] = if hi : i ∈ s then f i hi else d := by
  unfold indicator
  change _ = if hi : i ∈ s.1 then _ else _
  obtain ⟨l, hl⟩ := s.1.exists_rep
  simp_rw [← hl, Equiv.subtypeQuotientEquivQuotientSubtype_mk]
  dsimp
  rw [getElem_listIndicator]
  rfl

abbrev toOfFn [Fintype ι] (f : ι → α) : OfFn C ι α V f where
  ofFn := indicator C Finset.univ (fun i _ ↦ f i)
  getElem_ofFn _ _ := by
    convert (getElem_indicator _ _ _).trans <| dif_pos <| Finset.mem_univ _
    classical infer_instance

end AssocArray

class HasDefaultAssocDArray (ι : Type u) (α : Type v) (f : ι → α)
    (DefaultAssocDArray : outParam <| Type max u v)
    (V : outParam _) [Inhabited DefaultAssocDArray] where
  [toAssocDArray : AssocDArray DefaultAssocDArray ι α V f]

@[nolint unusedArguments]
def DefaultAssocDArray (ι : Type u) (α : Type v) (f : ι → α) {D : Type _} {V} [Inhabited D]
    [HasDefaultAssocDArray ι α f D V] :=
  D

instance {n α f} : HasDefaultAssocDArray (Fin n) α f (Batteries.Vector.WithDefault α n f)
    (fun _ i ↦ i < n) where

example {n α f} := DefaultAssocDArray (Fin n) α f
