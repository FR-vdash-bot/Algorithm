/-
Copyright (c) 2023 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Algorithm.Data.Classes.GetSet
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

instance : AssocDArray (Vector.WithDefault α n f) (Fin n) α f where
  set := set
  get := get
  get_set_eq := get_set_eq
  get_set_ne := get_set_ne
  get_default := get_default
  toDFinsupp' a := DFinsupp'.equivFunOnFintype.symm (get a)
  coe_toDFinsupp'_eq_get _ := DFinsupp'.coe_equivFunOnFintype_symm _

end Batteries.Vector

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

instance {n α f} : HasDefaultAssocDArray (Fin n) α f (Batteries.Vector.WithDefault α n f) where

example {n α f} := DefaultAssocDArray (Fin n) α f
