/-
Copyright (c) 2023 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Algorithm.Data.Classes.Collection

namespace Option

lemma isSome_map {α β : Type*} (f : α → β) (x : Option α) :
    (x.map f).isSome = x.isSome :=
  match x with | none | some _ => rfl

end Option

namespace List
variable {α : Type*} (l : List α)

lemma head?_isSome : (head? l).isSome = !l.isEmpty :=
  match l with | [] | _::_ => rfl

lemma tail?_isSome : (tail? l).isSome = !l.isEmpty :=
  match l with | [] | _::_ => rfl

instance : Decidable (l = []) :=
  match l with
  | [] => isTrue rfl
  | _::_ => isFalse (nomatch ·)

lemma isEmpty_eq_decide_eq_nil : l.isEmpty = decide (l = []) := by
  cases l <;> simp [isEmpty]

lemma isEmpty_eq_decide_length : l.isEmpty = decide (l.length = 0) := by
  cases l <;> simp [isEmpty]

lemma isEmpty_reverse : l.reverse.isEmpty = l.isEmpty := by
  rw [isEmpty_eq_decide_eq_nil, isEmpty_eq_decide_eq_nil]
  simp only [reverse_eq_nil]

lemma reverse_dropLast (l : List α) : l.dropLast.reverse = l.reverse.tail :=
  match l with
  | [] | [_] => rfl
  | x::_::_ => by
    rw [dropLast, reverse_cons x, reverse_cons x, reverse_dropLast (_::_),
      tail_append_of_ne_nil] <;> simp

end List

namespace Array

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

end Array

set_option linter.unusedVariables false in
@[nolint unusedArguments]
def StackLike.Aux.ofList {S : Type*} {α : outParam Type*} [Collection S α]
    {toList : S → List α}
    (isEmpty_toList : ∀ s, (toList s).isEmpty = Collection.isEmpty s)
    {push : S → α → S}
    (cons_toList : ∀ s a, (toList s).cons a = toList (push s a)) :
    List α → S :=
  fun l ↦ l.foldr (fun x l ↦ push l x) Collection.empty

@[simp]
lemma StackLike.Aux.toList_ofList {S : Type*} {α : outParam Type*} [Collection S α]
    {toList : S → List α}
    (isEmpty_toList : ∀ s, (toList s).isEmpty = Collection.isEmpty s)
    {push : S → α → S}
    (cons_toList : ∀ s a, (toList s).cons a = toList (push s a))
    (l) :
    toList (ofList isEmpty_toList cons_toList l) = l :=
  l.recOn (List.isEmpty_iff_eq_nil.mp ((isEmpty_toList _).trans Collection.isEmpty_empty))
    (fun _ _ ih ↦ (cons_toList _ _).symm.trans (congr_arg₂ _ rfl ih))

macro "stackLike_toList_ofList_tac" : tactic =>
  `(tactic| exact StackLike.Aux.toList_ofList _ _ _)

class StackLike (S : Type*) (α : outParam Type*) extends Collection S α where
  toList : S → List α
  coe_toList_eq_toMultiset s : ↑(toList s) = toMultiset s := by intro; rfl
  toArray : S → Array α
  toListRev_toArray a : (toArray a).toListRev = toList a
  length_toList s : (toList s).length = size s :=
    ((congr_arg Multiset.card (coe_toList_eq_toMultiset s))).trans
      (Collection.card_toMultiset_eq_size s)
  size_toArray s : (toArray s).size = size s :=
    Eq.trans (by simp [← toListRev_toArray]) (length_toList s)
  isEmpty_toList s : (toList s).isEmpty = isEmpty s :=
    ((List.isEmpty_eq_decide_length _).trans
      (by rw [decide_eq_decide, length_toList])).trans
      (Collection.isEmpty_eq_decide_size s).symm
  push : S → α → S
  cons_toList s a : (toList s).cons a = toList (push s a)
  peek? : S → Option α
  head?_toList s : (toList s).head? = peek? s
  pop : S → S
  tail_toList s : (toList s).tail = toList (pop s)
  peekD : S → α → α :=
    fun s d ↦ (peek? s).getD d
  peek s : isEmpty s = false → α :=
    fun h ↦ (peek? s).get (by rw [← head?_toList, List.head?_isSome, isEmpty_toList, h]; rfl)
  peekD_def s d : peekD s d = (peek? s).getD d := by intros; rfl
  peek_mem s h : peek s h ∈ peek? s := by simp
  ofList : List α → S := StackLike.Aux.ofList isEmpty_toList cons_toList
  toList_ofList l : toList (ofList l) = l := by stackLike_toList_ofList_tac
-- TODO: `ofStream`, not `ofList`? or not this name?
-- TODO: `toStream`?

attribute [simp] StackLike.coe_toList_eq_toMultiset

section
variable {α : Type*}

instance : StackLike (List α) α where
  toList := id
  toArray l := l.toArray.reverse
  toListRev_toArray := by simp
  push l a := List.cons a l
  cons_toList _ _ := rfl
  peek? := List.head?
  head?_toList _ := rfl
  pop := List.tail
  tail_toList _ := rfl
  peekD := List.headD
  peek l h := List.head l <| List.isEmpty_iff_eq_nil.not.mp <| (Bool.not_eq_true _).mpr h
  peekD_def := List.headD_eq_head?
  peek_mem _ _ := List.head?_eq_head _ _
  ofList := id
  toList_ofList _ := rfl

instance : StackLike (Array α) α where
  toList := Array.toListRev
  toArray := id
  toListRev_toArray _ := rfl
  push := Array.push
  cons_toList _ _ := by simp
  peek? := Array.back?
  head?_toList := Array.head?_toListRev
  pop := Array.pop
  tail_toList _ := by simp [List.reverse_dropLast]
  ofList l := l.toArray.reverse
  toList_ofList _ := by simp

end
