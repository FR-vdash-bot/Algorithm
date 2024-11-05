/-
Copyright (c) 2023 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Algorithm.Data.Classes.ToMultiset

variable {C α : Type*}

namespace List
variable (l : List α)

lemma not_isEmpty_iff {l : List α} : ¬l.isEmpty ↔ l ≠ [] :=
  isEmpty_iff.not

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
  rw [Array.back?, Array.get?_eq_get?_toList, getLast?_eq_getElem?]
  simp

end List

namespace Array
variable (a : Array α)

lemma isEmpty_toListRev : a.toListRev.isEmpty = a.isEmpty := by
  rw [toListRev_eq, List.isEmpty_reverse, isEmpty_toList]

lemma toList_length : a.toList.length = a.size := by
  rw [length_toList]

@[simp]
lemma get?_toList : a.toList.get? = a.get? := by
  ext i
  rw [get?_eq_get?_toList]

lemma getLast?_toList : a.toList.getLast? = a.back? := by
  rw [back?, get?_eq_get?_toList, List.getLast?_eq_getElem?]
  simp

lemma dropLast_toList : a.toList.dropLast = a.pop.toList := by
  simp

end Array

class ToList (C : Type*) (α : outParam Type*) extends Membership α C, Size C where
  toList : C → List α
  toArray : C → Array α
  toArray_eq_mk_toList a : toArray a = Array.mk (toList a)
  mem c a := a ∈ toList c
  mem_toList {x c} : x ∈ toList c ↔ x ∈ c := by rfl
  size_eq_length_toList c : size c = (toList c).length
export ToList (toList toArray toArray_eq_mk_toList mem_toList size_eq_length_toList)

attribute [simp] toArray_eq_mk_toList mem_toList

section ToList

instance : ToList (List α) α where
  toList := id
  toArray := Array.mk
  toArray_eq_mk_toList _ := rfl
  size_eq_length_toList _ := rfl

instance : ToList (Array α) α where
  toList := Array.toList
  toArray := id
  toArray_eq_mk_toList _ := rfl
  mem_toList := Array.mem_def.symm
  size_eq_length_toList _ := rfl

variable [ToList C α]

instance (priority := 100) ToList.toToMultiset : ToMultiset C α where
  toMultiset c := ↑(toList c)
  mem_toMultiset := mem_toList
  size_eq_card_toMultiset c := size_eq_length_toList c

section LawfulEmptyCollection
variable [EmptyCollection C]

lemma lawfulEmptyCollection_iff_toList :
    LawfulEmptyCollection C α ↔ toList (∅ : C) = [] := by
  simp_rw [lawfulEmptyCollection_iff, List.eq_nil_iff_forall_not_mem, mem_toList]

alias ⟨_, LawfulEmptyCollection.of_toList⟩ := lawfulEmptyCollection_iff_toList

@[simp]
lemma toList_empty [LawfulEmptyCollection C α] :
    toList (∅ : C) = [] := by
  rwa [← lawfulEmptyCollection_iff_toList]

end LawfulEmptyCollection

variable (c : C)

lemma size_eq_size_toArray : size c = (toArray c).size := by
  simp [size_eq_length_toList]

lemma length_toList : (toList c).length = size c :=
  (size_eq_length_toList c).symm

lemma size_toArray : (toArray c).size = size c :=
  (size_eq_size_toArray c).symm

@[simp]
lemma coe_toList : ↑(toList c) = toMultiset c := rfl

lemma isEmpty_toList : (toList c).isEmpty = isEmpty c := by
  rw [isEmpty_eq_decide_size, List.isEmpty_eq_decide_length, size_eq_length_toList]

end ToList

class Front (C : Type*) (α : outParam Type*) [ToList C α] where
  front? : C → Option α
  front?_def s : front? s = (toList s).head?
  frontD : C → α → α :=
    fun s d ↦ (front? s).getD d
  front (c : C) : ¬isEmpty c → α :=
    fun h ↦ (front? c).get (by rwa [front?_def, List.head?_isSome, ← List.not_isEmpty_iff,
      isEmpty_toList])
  frontD_def c d : frontD c d = (front? c).getD d := by intros; rfl
  front_mem c h : front c h ∈ front? c := by simp
export Front (front? front?_def frontD front frontD_def front_mem)

attribute [simp] front?_def frontD_def

lemma front?_isSome {C α : Type*} [ToList C α] [Front C α] {c : C} (h : ¬isEmpty c) :
    (front? c).isSome := by
  rwa [front?_def, List.head?_isSome, ← List.not_isEmpty_iff, isEmpty_toList]

@[simp]
lemma front_def {C α : Type*} [ToList C α] [Front C α] (c : C) (h : ¬isEmpty c) :
    front c h = (front? c).get (front?_isSome h) :=
  Option.some_injective _ (by simpa using (front_mem c h).symm)

class Back (C : Type*) (α : outParam Type*) [ToList C α] where
  back? : C → Option α
  back?_def s : back? s = (toList s).getLast?
  backD : C → α → α :=
    fun s d ↦ (back? s).getD d
  back (c : C) : ¬isEmpty c → α :=
    fun h ↦ (back? c).get (by rwa [back?_def, List.getLast?_isSome, ← List.not_isEmpty_iff,
      isEmpty_toList])
  backD_def c d : backD c d = (back? c).getD d := by intros; rfl
  back_mem c h : back c h ∈ back? c := by simp
export Back (back? back?_def backD back backD_def back_mem)

attribute [simp] back?_def backD_def

lemma back?_isSome [ToList C α] [Back C α] {c : C} (h : ¬isEmpty c) :
    (back? c).isSome := by
  rwa [back?_def, List.getLast?_isSome, ← List.not_isEmpty_iff, isEmpty_toList]

@[simp]
lemma back_def [ToList C α] [Back C α] (c : C) (h : ¬isEmpty c) :
    back c h = (back? c).get (back?_isSome h) :=
  Option.some_injective _ (by simpa using (back_mem c h).symm)

class PopFront (C : Type*) (α : outParam Type*) [ToList C α] where
  popFront : C → C
  toList_popFront s : toList (popFront s) = (toList s).tail
export PopFront (popFront toList_popFront)

attribute [simp] toList_popFront

class PopBack (C : Type*) (α : outParam Type*) [ToList C α] where
  popBack : C → C
  toList_popBack s : toList (popBack s) = (toList s).dropLast
export PopBack (popBack toList_popBack)

attribute [simp] toList_popBack

class PushFront (C : Type*) (α : outParam Type*) [ToList C α] where
  pushFront : C → α → C
  toList_pushFront s a : toList (pushFront s a) = List.cons a (toList s)
export PushFront (pushFront toList_pushFront)

attribute [simp] toList_popBack

class PushBack (C : Type*) (α : outParam Type*) [ToList C α] where
  pushBack : C → α → C
  toList_pushBack s a : toList (pushBack s a) = toList s ++ [a]
export PushBack (pushBack toList_pushBack)

attribute [simp] toList_pushBack

class LawfulAppend (C : Type*) (α : outParam Type*) [ToList C α] [Append C] : Prop where
  toList_append (s t : C) : toList (s ++ t) = toList s ++ toList t
export LawfulAppend (toList_append)

attribute [simp] toList_append

class ToList.RandomAccess (C : Type*) (α : outParam Type*) [ToList C α] where
  get (c : C) : Fin (size c) → α
  get_eq_get_toArray c i : get c i = (toArray c).get (i.cast (size_eq_size_toArray c))
export ToList.RandomAccess (get_eq_get_toArray)

section ToList
variable {C α : Type*} [ToList C α]

instance (priority := 100) LawfulAppend.toMergeable [Append C] [LawfulAppend C α] :
    Mergeable C α where
  merge s t := s ++ t
  toMultiset_merge s t := congr_arg Multiset.ofList (toList_append s t)

lemma ToList.RandomAccess.get_toArray [ToList.RandomAccess C α] (c : C) (i) :
    (toArray c).get i = ToList.RandomAccess.get c (i.cast (size_toArray c)) := by
  rw [get_eq_get_toArray]; rfl

end ToList

section List

instance : Front (List α) α where
  front? := List.head?
  front?_def _ := rfl
  frontD := List.headD
  front l h := l.head <| List.not_isEmpty_iff.mp h
  frontD_def := List.headD_eq_head?
  front_mem _ _ := List.head?_eq_head _

instance : PopFront (List α) α where
  popFront := List.tail
  toList_popFront _ := rfl

instance : PushFront (List α) α where
  pushFront c a := List.cons a c
  toList_pushFront _ _ := rfl

instance : LawfulAppend (List α) α where
  toList_append _ _ := rfl

end List

section Array

instance : Front (Array α) α where
  front? c := c.get? 0
  front?_def c := by
    dsimp only
    rw [← Array.get?_toList, List.get?_zero]
    rfl
  frontD c := c.getD 0
  front c h := c.get ⟨0, by simp_rw [isEmpty_iff_size_eq_zero, size] at h; omega⟩
  frontD_def := by simp
  front_mem _ := by simp [Array.get?, size, ← ne_eq, ← List.length_pos_iff_ne_nil]

instance : Back (Array α) α where
  back? := Array.back?
  back?_def c := (Array.getLast?_toList c).symm

instance : PopBack (Array α) α where
  popBack := Array.pop
  toList_popBack := Array.pop_toList

instance : PushBack (Array α) α where
  pushBack := Array.push
  toList_pushBack := by simp [toList]

instance : LawfulAppend (Array α) α where
  toList_append := Array.toList_append

instance : ToList.RandomAccess (Array α) α where
  get := Array.get
  get_eq_get_toArray _ _ := rfl

end Array
