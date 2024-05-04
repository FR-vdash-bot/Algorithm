/-
Copyright (c) 2023 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Algorithm.Data.DFinsupp'.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Setoid.Basic
import Std.Data.Array.Lemmas

namespace Array
variable {α : Type*} {n : ℕ}

lemma get_fin_set (a : Array α) (i : Fin a.size) (v : α) (j : Fin (set a i v).size) :
    (a.set i v).get j = if i.1 = j.1 then v else a[j.1] := by
  rw [get_eq_getElem, get_set]

end Array

def ArrayVector (α : Type*) (n : ℕ) := {a : Array α // a.size = n}

namespace ArrayVector
variable {α : Type*} {n : ℕ}

def ofFn (f : Fin n → α) : ArrayVector α n :=
  ⟨.ofFn f, Array.size_ofFn f⟩

instance {α n} [Inhabited α] : Inhabited (ArrayVector α n) where
  default := .ofFn fun _ ↦ default

def get (a : ArrayVector α n) (i : Fin n) : α :=
  a.1.get (i.cast a.2.symm)

def set (a : ArrayVector α n) (i : Fin n) (v : α) : ArrayVector α n :=
  ⟨a.1.set (i.cast a.2.symm) v, (Array.size_set _ _ _).trans a.2⟩

lemma get_set (a : ArrayVector α n) (i : Fin n) (v : α) :
    (a.set i v).get = Function.update a.get i v := by
  unfold get set
  simp_rw [Array.get_fin_set]
  ext; simp [Function.update, Fin.val_eq_val, eq_comm (a := i)]

@[simp]
lemma get_ofFn (f : Fin n → α) : (ofFn f).get = f := by
  ext; simp [ofFn, get]

@[simp]
lemma get_default [Inhabited α] : (default : ArrayVector α n).get = default :=
  get_ofFn _

end ArrayVector

class AssocArray.ReadOnly (C : Type*) (ι : outParam Type*)
    (α : outParam Type*) [Inhabited α] where
  get : C → ι → α
  toDFinsupp' : C → ι →₀' [α, default]
  coe_toDFinsupp'_eq_get : ∀ a : C, ⇑(toDFinsupp' a) = get a
export AssocArray.ReadOnly (toDFinsupp' coe_toDFinsupp'_eq_get)

/-- `AssocArray C ι α` is a data structure that acts like a finitely supported function
  `ι →₀' [α, default]` with single point update operation. -/
class AssocArray (C : Type*) [Inhabited C] (ι : outParam Type*)
    (α : outParam Type*) [Inhabited α] extends AssocArray.ReadOnly C ι α where
  set : C → ι → α → C
  get_set : [DecidableEq ι] → ∀ a i v, get (set a i v) = Function.update (get a) i v
  get_default : get default = default

namespace AssocArray

export ReadOnly (get toDFinsupp' coe_toDFinsupp'_eq_get)

attribute [simp] AssocArray.get_set AssocArray.get_default coe_toDFinsupp'_eq_get

section ReadOnly
variable {C : Type*} {ι : Type*} {α : Type*} [Inhabited α]
variable [AssocArray.ReadOnly C ι α]

instance : GetElem C ι α fun _ _ ↦ True where
  getElem a i _ := AssocArray.get a i

@[simp]
lemma get_eq_getElem (a : C) (i : ι) : get a i = a[i] := rfl

end ReadOnly

variable {C : Type*} [Inhabited C] {ι : Type*} {α : Type*} [Inhabited α]
  [AssocArray C ι α]

lemma toDFinsupp'_apply_eq_getElem (a : C) (i : ι) : toDFinsupp' a i = a[i] := by simp

@[simp]
lemma getElem_set [DecidableEq ι] (a : C) (i : ι) (v : α) (j : ι) :
    (set a i v)[j] = Function.update (get a) i v j :=
  congr_fun (get_set a i v) j

@[simp]
lemma getElem_default (i : ι) :
    (default : C)[i] = Function.const _ default i :=
  congr_fun get_default i

@[simp]
lemma toDFinsupp'_set [DecidableEq ι] (a : C) (i : ι) (v : α) :
    toDFinsupp' (set a i v) = (toDFinsupp' a).update i v := by
  ext; simp

@[simp]
lemma toDFinsupp'_default :
    toDFinsupp' (default : C) = default := by
  ext; simp

end AssocArray

namespace ArrayVector
variable {α : Type*} {n : ℕ}

instance [Inhabited α] : AssocArray (ArrayVector α n) (Fin n) α where
  set := set
  get := get
  get_set a i v := by convert get_set a i v
  get_default := get_default
  toDFinsupp' a := DFinsupp'.equivFunOnFintype.symm (get a)
  coe_toDFinsupp'_eq_get _ := DFinsupp'.coe_equivFunOnFintype_symm _

end ArrayVector

namespace AssocArray

class Ext (C : Type*) [Inhabited C] (ι : outParam Type*)
    (α : outParam Type*) [Inhabited α] [AssocArray C ι α] : Prop where
  ext : ∀ {m₁ m₂ : C}, get m₁ = get m₂ → m₁ = m₂

variable {C : Type*} [Inhabited C] {ι : Type*} {α : Type*} [Inhabited α] [AssocArray C ι α]

variable (C)

protected def Quotient := @Quotient C (Setoid.ker get)

instance : Inhabited (AssocArray.Quotient C) :=
  inferInstanceAs <| Inhabited (@Quotient C (Setoid.ker get))

instance : AssocArray (AssocArray.Quotient C) ι α where
  set q i v := q.map' (set · i v) (by classical exact
    fun _ _ hm ↦ (Eq.congr (get_set _ _ _) (get_set _ _ _)).mpr (by rw [hm]))
  get := Quotient.lift get (fun _ _ ↦ id)
  get_set q i v := q.inductionOn (fun _ ↦ get_set _ _ _)
  get_default := get_default
  toDFinsupp' := Quotient.lift toDFinsupp' (fun _ _ ↦ by
    simpa only [DFunLike.ext'_iff, coe_toDFinsupp'_eq_get] using id)
  coe_toDFinsupp'_eq_get a := by
    induction a using Quotient.ind
    exact coe_toDFinsupp'_eq_get _

instance : Ext (AssocArray.Quotient C) ι α where
  ext {m₁ m₂} := m₂.inductionOn <| m₁.inductionOn (fun _ _ ha ↦ Quotient.sound ha)
export Ext (ext)

def listIndicator (l : List ι) (f : ∀ i ∈ l, α) : C :=
  match l with
  | [] => default
  | (i :: l) => set (listIndicator l (fun i hi ↦ f i (List.mem_cons_of_mem _ hi)))
    i (f i (List.mem_cons_self _ _))

variable {C}

lemma get_listIndicator [DecidableEq ι] (l : List ι) (f : ∀ i ∈ l, α) :
    get (listIndicator C l f) = (fun i ↦ if hi : i ∈ l then f i hi else default) :=
  match l with
  | [] => by ext; simp [listIndicator, get_default, Function.const]
  | (i :: l) => by
    ext j
    rw [listIndicator, get_set, Function.update_apply]
    split_ifs with h₁ h₂ h₂
    · simp [h₁]
    · simp [h₁] at h₂
    · simp_rw [get_listIndicator, dif_pos (List.mem_of_ne_of_mem h₁ h₂)]
    · simp_rw [get_listIndicator, dif_neg (List.not_mem_of_not_mem_cons h₂)]

variable [Ext C ι α]
variable (C)

def indicator (s : Finset ι) (f : ∀ i ∈ s, α) : C :=
  let this := Equiv.subtypeQuotientEquivQuotientSubtype (fun l : List ι ↦ ↑l = s.1)
    (fun m ↦ m = s.1) (fun i ↦ Iff.rfl) (fun _ _ ↦ Iff.rfl) ⟨s.1, rfl⟩
  this.liftOn (fun l ↦ listIndicator C l (fun i hi ↦ f i (l.2 ▸ hi : i ∈ s.1)))
    (fun l₁ l₂ hl ↦ ext <| by classical simp_rw [get_listIndicator, List.Perm.mem_iff hl])

variable {C}

lemma get_indicator [DecidableEq ι] (s : Finset ι) (f : ∀ i ∈ s, α) :
    get (indicator C s f) = (fun i ↦ if hi : i ∈ s then f i hi else default) := by
  unfold indicator
  change _ = (fun i ↦ if hi : i ∈ s.1 then _ else _)
  obtain ⟨l, hl⟩ := s.1.exists_rep
  simp_rw [← hl]
  rw [Equiv.subtypeQuotientEquivQuotientSubtype_mk]
  dsimp
  rw [get_listIndicator]
  rfl

variable (C)

def ofFn [Fintype ι] (f : ι → α) : C := indicator C Finset.univ (fun i _ ↦ f i)

variable {C}

lemma get_ofFn [DecidableEq ι] [Fintype ι] (f : ι → α) :
    get (ofFn C f) = f :=
  (get_indicator _ _).trans <| funext fun _ ↦ dif_pos <| Finset.mem_univ _

end AssocArray
