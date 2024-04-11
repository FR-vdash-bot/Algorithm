/-
Copyright (c) 2023 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Algorithm.Data.Classes.ToMultiset

namespace List
variable {α : Type*} (l : List α)

-- #check isEmpty_iff_eq_nil
lemma not_isEmpty_iff_ne_nil {l : List α} : ¬l.isEmpty ↔ l ≠ [] :=
  isEmpty_iff_eq_nil.not

-- #check getLast?_isSome
lemma head?_isSome : (head? l).isSome ↔ l ≠ [] :=
  match l with | [] | _::_ => by simp

lemma tail?_isSome : (tail? l).isSome ↔ l ≠ [] :=
  match l with | [] | _::_ => by simp

lemma head?_isSome' : (head? l).isSome = !l.isEmpty :=
  match l with | [] | _::_ => rfl

lemma tail?_isSome' : (tail? l).isSome = !l.isEmpty :=
  match l with | [] | _::_ => rfl

instance : Decidable (l = []) :=
  match l with
  | [] => isTrue rfl
  | _::_ => isFalse nofun

lemma isEmpty_eq_decide_eq_nil : l.isEmpty = decide (l = []) := by
  cases l <;> simp [isEmpty]

lemma isEmpty_eq_decide_length : l.isEmpty = decide (l.length = 0) := by
  cases l <;> simp [isEmpty]

lemma isEmpty_reverse : l.reverse.isEmpty = l.isEmpty := by
  rw [isEmpty_eq_decide_eq_nil, isEmpty_eq_decide_eq_nil]
  simp only [reverse_eq_nil_iff]

lemma reverse_dropLast (l : List α) : l.dropLast.reverse = l.reverse.tail :=
  match l with
  | [] | [_] => rfl
  | x::_::_ => by
    rw [dropLast, reverse_cons x, reverse_cons x, reverse_dropLast (_::_),
      tail_append_of_ne_nil] <;> simp

@[simp]
lemma back?_toArray : l.toArray.back? = l.getLast? := by
  rw [Array.back?, Array.get?_eq_data_get?, getLast?_eq_get?]
  simp

end List

namespace Array
variable {α : Type*} (a : Array α)

lemma isEmpty_data {α : Type*} (a : Array α) : a.data.isEmpty = a.isEmpty := by
  rw [List.isEmpty_eq_decide_length, isEmpty]

lemma isEmpty_toList {α : Type*} (a : Array α) : a.toList.isEmpty = a.isEmpty := by
  rw [isEmpty_data, toList_eq]

lemma isEmpty_toListRev {α : Type*} (a : Array α) : a.toListRev.isEmpty = a.isEmpty := by
  rw [toListRev_eq, List.isEmpty_reverse, isEmpty_data]

@[simp]
lemma length_data {α : Type*} (a : Array α) : a.data.length = a.size := rfl

lemma length_toList {α : Type*} (a : Array α) : a.toList.length = a.size := by
  rw [toList_eq, length_data]

@[simp]
lemma get?_data {α : Type*} (a : Array α) : a.data.get? = a.get? := by
  ext i
  rw [Array.get?_eq_data_get?]

lemma get?_toList {α : Type*} (a : Array α) : a.toList.get? = a.get? := by
  rw [toList_eq, get?_data]

lemma get?_toListRev {α : Type*} (a : Array α) (i : Nat) (h : i < a.size) :
    a.toListRev.get? i = a.get? (a.size - 1 - i) := by
  rw [toListRev_eq, List.get?_reverse _ (by rwa [length_data]), get?_data]

lemma head?_toListRev {α : Type*} (a : Array α) : a.toListRev.head? = a.back? := by
  cases a.size.eq_zero_or_pos
  case inl h =>
    rw [toListRev_eq, back?, ← get?_data]
    simp [List.length_eq_zero.mp h]
  case inr h =>
    rw [← List.get?_zero, get?_toListRev _ _ h, Nat.sub_zero]
    rfl

lemma getLast?_toList (a : Array α) : a.toList.getLast? = a.back? := by
  rw [back?, get?_eq_data_get?, List.getLast?_eq_get?]
  simp

@[simp]
lemma getLast?_data (a : Array α) : a.data.getLast? = a.back? := by
  simp [← getLast?_toList]

lemma dropLast_toList (a : Array α) : a.toList.dropLast = a.pop.toList := by
  simp

end Array

class ToList (C : Type*) (α : outParam Type*) extends Size C α where
  toList : C → List α
  toArray : C → Array α
  toArray_toList a : (toArray a).toList = toList a
  length_toList c : (toList c).length = size c
export ToList (toList toArray toArray_toList length_toList)

section ToList
variable {C α : Type*} [ToList C α] (c : C)

instance (priority := 100) : ToMultiset C α where
  toMultiset c := ↑(toList c)
  card_toMultiset_eq_size c := length_toList c

@[simp]
lemma coe_toList_eq_toMultiset : ↑(toList c) = toMultiset c := rfl

lemma isEmpty_toList : (toList c).isEmpty = isEmpty c := by
  rw [isEmpty_eq_decide_size, List.isEmpty_eq_decide_length, length_toList]

@[simp]
lemma mem_toList (v : α) : v ∈ toList c ↔ v ∈ c := .rfl

end ToList

class Front (C : Type*) (α : outParam Type*) [ToList C α] where
  front? : C → Option α
  head?_toList s : (toList s).head? = front? s
  frontD : C → α → α :=
    fun s d ↦ (front? s).getD d
  front (c : C) : ¬isEmpty c → α :=
    fun h ↦ (front? c).get (by rwa [← head?_toList, List.head?_isSome, ← List.not_isEmpty_iff_ne_nil, isEmpty_toList])
  frontD_def c d : frontD c d = (front? c).getD d := by intros; rfl
  front_mem c h : front c h ∈ front? c := by simp
export Front (front? head?_toList frontD front frontD_def front_mem)

class Back (C : Type*) (α : outParam Type*) [ToList C α] where
  back? : C → Option α
  getLast?_toList s : (toList s).getLast? = back? s
  backD : C → α → α :=
    fun s d ↦ (back? s).getD d
  back (c : C) : ¬isEmpty c → α :=
    fun h ↦ (back? c).get (by rwa [← getLast?_toList, List.getLast?_isSome, ← List.not_isEmpty_iff_ne_nil, isEmpty_toList])
  backD_def c d : backD c d = (back? c).getD d := by intros; rfl
  back_mem c h : back c h ∈ back? c := by simp
export Back (back? getLast?_toList backD back backD_def back_mem)

class PopFront (C : Type*) (α : outParam Type*) [ToList C α] where
  popFront : C → C
  tail_toList s : (toList s).tail = toList (popFront s)
export PopFront (popFront tail_toList)

class PopBack (C : Type*) (α : outParam Type*) [ToList C α] where
  popBack : C → C
  dropLast_toList s : (toList s).dropLast = toList (popBack s)
export PopBack (dropLast_toList dropLast_toList)

class PushFront (C : Type*) (α : outParam Type*) [ToList C α] where
  pushFront : C → α → C
  cons_toList s a : List.cons a (toList s) = toList (pushFront s a)
export PopFront (popFront tail_toList)

class PushBack (C : Type*) (α : outParam Type*) [ToList C α] where
  pushBack : C → α → C
  toList_append_singleton s a : toList s ++ [a] = toList (pushBack s a)
export PopFront (popFront tail_toList)

section
variable {α : Type*}

instance : ToList (List α) α where
  toList := id
  toArray := List.toArray
  toArray_toList _ := by simp
  length_toList _ := rfl

instance : Front (List α) α where
  front? := List.head?
  head?_toList _ := rfl
  frontD := List.headD
  front l h := l.head <| List.not_isEmpty_iff_ne_nil.mp h
  frontD_def := List.headD_eq_head?
  front_mem _ _ := List.head?_eq_head _ _

instance : PopFront (List α) α where
  popFront := List.tail
  tail_toList _ := rfl

instance : PushFront (List α) α where
  pushFront c a := List.cons a c
  cons_toList _ _ := rfl

instance : ToList (Array α) α where
  toList := Array.toList
  toArray := id
  toArray_toList _ := rfl
  length_toList _ := by simp [size]

instance : Back (Array α) α where
  back? := Array.back?
  getLast?_toList := Array.getLast?_toList

instance : PopBack (Array α) α where
  popBack := Array.pop
  dropLast_toList := Array.dropLast_toList

instance : PushBack (Array α) α where
  pushBack := Array.push
  toList_append_singleton _ _ := by simp [toList]

end
