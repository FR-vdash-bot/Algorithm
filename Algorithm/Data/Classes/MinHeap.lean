/-
Copyright (c) 2024 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Algorithm.Data.Classes.ToMultiset
import Mathlib.Data.Multiset.Lattice

namespace Multiset -- should be in mathlb
variable {α : Type*} [SemilatticeInf α] [OrderTop α]

@[simp]
theorem inf_eq_top {m : Multiset α} : m.inf = ⊤ ↔ ∀ a ∈ m, a = ⊤ := by
  rw [le_antisymm_iff]
  simp

end Multiset

class MinHeap (C : Type*) (α : outParam Type*) [LinearOrder α] extends
    ToMultiset C α,
    EmptyCollection C, ToMultiset.LawfulEmptyCollection C α,
    Insert α C, ToMultiset.LawfulInsert C α where
  head? : C → WithTop α
  head?_def c : head? c = ((toMultiset c).map WithTop.some).inf
  headD : C → α → α :=
    fun s d ↦ (head? s).getD d
  head (c : C) : ¬isEmpty c → α :=
    fun h ↦ (head? c).untop fun hc ↦ h (by
      rw [isEmpty_iff_size_eq_zero, size_eq_card_toMultiset, Multiset.card_eq_zero,
        Multiset.eq_zero_iff_forall_not_mem]
      simpa [head?_def] using hc)
  headD_def c d : headD c d = (head? c).getD d := by intros; rfl
  head_eq_head? c h : head c h = head? c := by simp
  tail : C → C
  toMultiset_tail c : toMultiset (tail c) =
    if h : isEmpty c then 0 else (toMultiset c).erase (head c h)
  deleteMin : C → Option (α × C) := fun c ↦ if h : isEmpty c then none else
    some (head c h, tail c)
  deleteMin_def c : deleteMin c = if h : isEmpty c then none else
    some (head c h, tail c) := by rfl

namespace MinHeap

attribute [simp] head?_def headD_def toMultiset_tail deleteMin_def

variable {C α : Type*} [LinearOrder α] [MinHeap C α] {c : C}

lemma head?_ne_top (h : ¬isEmpty c) :
    (MinHeap.head? c) ≠ ⊤ := fun hc ↦ h (by
  rw [isEmpty_iff_size_eq_zero, size_eq_card_toMultiset, Multiset.card_eq_zero,
    Multiset.eq_zero_iff_forall_not_mem]
  simpa [head?_def] using hc)

@[simp]
lemma head_def (h : ¬isEmpty c) :
    MinHeap.head c h = (head? c).untop (head?_ne_top h) :=
  WithTop.coe_injective (by simpa using MinHeap.head_eq_head? c h)

end MinHeap
