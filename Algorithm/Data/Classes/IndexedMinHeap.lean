/-
Copyright (c) 2023 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Algorithm.Data.Classes.AssocArray
import Mathlib.Data.Finset.Lattice
import Mathlib.Data.Prod.Lex

class IndexedMinHeap (H : Type*) (ι : outParam Type*) [DecidableEq ι]
    (α : outParam Type*) [LinearOrder α] extends AssocArray H ι (WithTop α) where
  minIdx : H → ι
  get_minIdx_le h (i : ι) : h[minIdx h] ≤ h[i]

namespace ArrayVector
variable {α : Type*} [LinearOrder α] {n : ℕ} [NeZero n]

def minAux (a : ArrayVector (WithTop α) n) : Lex (WithTop α × Fin n) :=
  (⊤ : Finset (Fin n)).inf' ⟨0, Finset.mem_univ 0⟩ (fun i ↦ toLex (a[i], i))

def minIdx (a : ArrayVector (WithTop α) n) : Fin n :=
  a.minAux.2

def minIdx_spec (a : ArrayVector (WithTop α) n) (i : Fin n) :
    a[a.minIdx] < a[i] ∨ a[a.minIdx] = a[i] ∧ a.minIdx ≤ i := by
  have : a.minAux.1 = a[a.minIdx]
  · unfold minIdx minAux
    obtain ⟨i, -, h⟩ := (⊤ : Finset (Fin n)).exists_mem_eq_inf'
      ⟨0, Finset.mem_univ 0⟩ (fun i ↦ toLex (a[i], i))
    rw [Prod.eq_iff_fst_eq_snd_eq] at h
    obtain ⟨h : _ = a[i], rfl : _ = i⟩ := h
    exact h
  rw [← this]
  apply (Prod.Lex.le_iff _ (a[i], i)).mp
  exact Finset.inf'_le _ (Finset.mem_univ _)

def minIdx_le (a : ArrayVector (WithTop α) n) (i : Fin n) :
    a[a.minIdx] ≤ a[i] :=
  (a.minIdx_spec i).elim LT.lt.le (fun ⟨h, _⟩ ↦ h.le)

instance [NeZero n] : IndexedMinHeap (ArrayVector (WithTop α) n) (Fin n) α where
  minIdx a := ((⊤ : Finset (Fin n)).inf' ⟨0, Finset.mem_univ 0⟩ (fun i ↦ toLex (a[i], i))).2
  get_minIdx_le a i := a.minIdx_le i

end ArrayVector
