/-
Copyright (c) 2023 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Algorithm.Data.Classes.AssocArray
import Algorithm.Data.Classes.ToList
import Mathlib.Data.Prod.Lex

class IndexedMinHeap (C : Type*) [Inhabited C] (ι : outParam Type*)
    (α : outParam Type*) [Inhabited α] [LinearOrder α] extends AssocArray C ι α where
  minIdx : C → ι
  getElem_minIdx_le h (i : ι) : h[minIdx h] ≤ h[i]
  decreaseKey (c : C) (i : ι) : ∀ v < c[i], C := fun v _ ↦ update c i v
  decreaseKey_eq_update (c : C) (i : ι) v (h : v < c[i]) : decreaseKey c i v h = update c i v := by
    intros; rfl
export IndexedMinHeap (minIdx getElem_minIdx_le decreaseKey decreaseKey_eq_update)

attribute [simp] decreaseKey_eq_update

section IndexedMinHeap
variable {C : Type*} [Inhabited C] {ι : Type*} {α : Type*} [Inhabited α] [LinearOrder α]
  [IndexedMinHeap C ι α]

def decreaseKeyD (c : C) (i : ι) (v : α) : C :=
  if c[i] ≤ v then c else AssocArray.update c i v

@[simp]
lemma decreaseKeyD_getElem [DecidableEq ι] [OrderTop α]
    (c : C) (i : ι) (v : α) (j : ι) :
    (decreaseKeyD c i v)[j] = if i = j then min c[j] v else c[j] := by
  split_ifs with h <;> rw [decreaseKeyD, apply_ite (fun c : C ↦ c[j])]
  · simp [h, min_def]
  · simp [Ne.symm h]

def decreaseKeysD {ια : Type*} [ToList ια (ι × α)] (c : C) (iv : ια) : C :=
  (toList iv).foldl (fun c ⟨i, v⟩ ↦ decreaseKeyD c i v) c

@[simp]
lemma decreaseKeysD_getElem [DecidableEq ι] [OrderTop α] {ια : Type*} [ToList ια (ι × α)]
    (c : C) (iv : ια) (i : ι) :
    (decreaseKeysD c iv)[i] = min c[i] ((toMultiset iv).filterMap
      (fun iv ↦ if iv.1 = i then some iv.2 else none)).inf := by
  rw [← coe_toList, decreaseKeysD]
  generalize toList iv = l
  simp only [Multiset.filterMap_coe, Multiset.inf_coe]
  induction l generalizing c with
  | nil => simp
  | cons hd tl ih =>
    rw [List.foldl_cons, ih, decreaseKeyD_getElem]
    split_ifs with h
    · simp only [List.filterMap_cons, h, List.foldr_cons, min_assoc]
      congr
    · simp [h]

end IndexedMinHeap

namespace ArrayVector
variable {α : Type*} [Inhabited α] [LinearOrder α] {n : ℕ} [NeZero n]

def minAux (a : ArrayVector α n) : Lex (α × Fin n) :=
  (⊤ : Finset (Fin n)).inf' ⟨0, Finset.mem_univ 0⟩ (fun i ↦ toLex (a[i], i))

def minIdx (a : ArrayVector α n) : Fin n :=
  a.minAux.2

def minIdx_spec (a : ArrayVector α n) (i : Fin n) :
    a[a.minIdx] < a[i] ∨ a[a.minIdx] = a[i] ∧ a.minIdx ≤ i := by
  have : a.minAux.1 = a[a.minIdx] := by
    unfold minIdx minAux
    obtain ⟨i, -, h⟩ := (⊤ : Finset (Fin n)).exists_mem_eq_inf'
      ⟨0, Finset.mem_univ 0⟩ (fun i ↦ toLex (a[i], i))
    rw [Prod.eq_iff_fst_eq_snd_eq] at h
    obtain ⟨h : _ = a[i], rfl : _ = i⟩ := h
    exact h
  rw [← this]
  apply (Prod.Lex.le_iff _ (a[i], i)).mp
  exact Finset.inf'_le _ (Finset.mem_univ _)

def minIdx_le (a : ArrayVector α n) (i : Fin n) :
    a[a.minIdx] ≤ a[i] :=
  (a.minIdx_spec i).elim LT.lt.le (fun ⟨h, _⟩ ↦ h.le)

instance [NeZero n] : IndexedMinHeap (ArrayVector α n) (Fin n) α where
  minIdx a := ((⊤ : Finset (Fin n)).inf' ⟨0, Finset.mem_univ 0⟩ (fun i ↦ toLex (a[i], i))).2
  getElem_minIdx_le a i := a.minIdx_le i

end ArrayVector
