/-
Copyright (c) 2023 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Setoid.Basic
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

class Ext (ι : outParam <| Type _) [DecidableEq ι]
    (α : outParam <| Type _) [Inhabited α] (M : Type _) [AssocArray ι α M] where
  ext : ∀ {m₁ m₂ : M}, get m₁ = get m₂ → m₁ = m₂

variable {ι : Type _} [DecidableEq ι] {α : Type _} [Inhabited α] {M : Type _} [AssocArray ι α M]

variable (M)

def Quotient := @_root_.Quotient M (Setoid.ker get)

instance : AssocArray ι α (Quotient M) where
  empty := ⟦empty⟧
  set q i v := q.map' (set · i v) (fun _ _ hm ↦ (Eq.congr get_set get_set).mpr (by rw [hm]))
  get := Quotient.lift get (fun _ _ ↦ id)
  get_set {q i v} := q.inductionOn (fun _ ↦ get_set)
  get_empty := get_empty

instance : Ext ι α (Quotient M) where
  ext {m₁ m₂} := m₂.inductionOn <| m₁.inductionOn (fun _ _ ha ↦ Quotient.sound ha)
export Ext (ext)

def listIndicator (l : List ι) (f : ∀ i ∈ l, α) : M :=
  match l with
  | [] => empty
  | (i :: l) => set (listIndicator l (fun i hi ↦ f i (List.mem_cons_of_mem _ hi)))
    i (f i (List.mem_cons_self _ _))

variable {M}

lemma get_listIndicator (l : List ι) (f : ∀ i ∈ l, α) :
    get (listIndicator M l f) = (fun i ↦ if hi : i ∈ l then f i hi else default) :=
  match l with
  | [] => by simp [listIndicator, get_empty, Function.const]
  | (i :: l) => by
    ext j
    rw [listIndicator, get_set, Function.update_apply]
    split_ifs with h₁ h₂
    · simp [h₁]
    · simp [h₁] at h₂
    · rename_i h₂ -- a `split_ifs` bug
      simp_rw [get_listIndicator, dif_pos (List.mem_of_ne_of_mem h₁ h₂)]
    · rename_i h₂ -- a `split_ifs` bug
      simp_rw [get_listIndicator, dif_neg (List.not_mem_of_not_mem_cons h₂)]

variable [Ext ι α M]
variable (M)

def indicator (s : Finset ι) (f : ∀ i ∈ s, α) : M :=
  let this := Equiv.subtypeQuotientEquivQuotientSubtype (fun l : List ι ↦ ↑l = s.1)
    (fun m ↦ m = s.1) (fun i ↦ Iff.rfl) (fun _ _ ↦ Iff.rfl) ⟨s.1, rfl⟩
  this.liftOn (fun l ↦ listIndicator M l (fun i hi ↦ f i (l.2 ▸ hi : i ∈ s.1)))
    (fun l₁ l₂ hl ↦ ext <| by simp_rw [get_listIndicator, List.Perm.mem_iff hl])

variable {M}

lemma get_indicator (s : Finset ι) (f : ∀ i ∈ s, α) :
    get (indicator M s f) = (fun i ↦ if hi : i ∈ s then f i hi else default) := by
  unfold indicator
  change _ = (fun i ↦ if hi : i ∈ s.1 then _ else _)
  obtain ⟨l, hl⟩ := s.1.exists_rep
  simp_rw [← hl]
  rw [Equiv.subtypeQuotientEquivQuotientSubtype_mk]
  dsimp
  rw [get_listIndicator]
  rfl

variable (M)

def ofFun [Fintype ι] (f : ι → α) : M := indicator M Finset.univ (fun i _ ↦ f i)

variable {M}

lemma get_ofFun [Fintype ι] (f : ι → α) :
    get (ofFun M f) = f :=
  (get_indicator _ _).trans <| funext fun _ ↦ dif_pos <| Finset.mem_univ _

end AssocArray
