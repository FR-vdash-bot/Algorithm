/-
Copyright (c) 2023 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Algorithm.Data.Classes.AssocArray
import Algorithm.Data.Classes.MinHeap
import Algorithm.Data.Classes.ToList
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Prod.Lex

class IndexedMinHeap (C : Type*) [Inhabited C] (ι : outParam Type*)
    (α : outParam Type*) [Preorder α] [IsTotal α (· ≤ ·)] [OrderTop α] extends
    AssocDArray C ι α fun _ ↦ ⊤ where
  minIdx : C → ι
  getElem_minIdx_le c (i : ι) : c[minIdx c] ≤ c[i]
  decreaseKey (c : C) (i : ι) : ∀ v < c[i], C := fun v _ ↦ c[i ↦ v]
  decreaseKey_eq_set (c : C) (i : ι) v (h : v < c[i]) : decreaseKey c i v h = c[i ↦ v] := by
    intros; rfl
export IndexedMinHeap (minIdx getElem_minIdx_le decreaseKey decreaseKey_eq_set)

attribute [simp] decreaseKey_eq_set

section IndexedMinHeap
variable {C : Type*} [Inhabited C] {ι : Type*} {α : Type*} [LinearOrder α] [OrderTop α]
  [IndexedMinHeap C ι α]

def decreaseKeyD (c : C) (i : ι) (v : α) : C :=
  if c[i] ≤ v then c else c[i ↦ v]

@[simp]
lemma decreaseKeyD_getElem [DecidableEq ι]
    (c : C) (i : ι) (v : α) (j : ι) :
    (decreaseKeyD c i v)[j] = if i = j then min c[j] v else c[j] := by
  split_ifs with h <;> rw [decreaseKeyD, apply_ite (fun c : C ↦ c[j])]
  · simp [h, min_def]
  · simp [h]

def decreaseKeysD {ια : Type*} [ToList ια (ι × α)] (c : C) (iv : ια) : C :=
  (toList iv).foldl (fun c ⟨i, v⟩ ↦ decreaseKeyD c i v) c

@[simp]
lemma decreaseKeysD_getElem [DecidableEq ι] {ια : Type*} [ToList ια (ι × α)]
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

namespace Vector
variable {α : Type*} [LinearOrder α] {n : ℕ} [NeZero n] {d : Fin n → α}

section ReadOnly

variable [AssocDArray.ReadOnly (Vector α n) (Fin n) α d]

abbrev minAux (a : Vector α n) : Lex (α × Fin n) :=
  (⊤ : Finset (Fin n)).inf' ⟨0, Finset.mem_univ 0⟩ (fun i ↦ toLex (a[i], i))

@[inline]
def minIdx (a : Vector α n) : Fin n :=
  a.minAux.2

lemma minIdx_spec (a : Vector α n) (i : Fin n) :
    a[a.minIdx] < a[i] ∨ a[a.minIdx] = a[i] ∧ a.minIdx ≤ i := by
  have : (ofLex a.minAux).1 = a[a.minIdx] := by
    unfold minIdx minAux
    obtain ⟨i, -, h⟩ := (⊤ : Finset (Fin n)).exists_mem_eq_inf'
      ⟨0, Finset.mem_univ 0⟩ (fun i ↦ toLex (a[i], i))
    rw [Prod.eq_iff_fst_eq_snd_eq] at h
    obtain ⟨h : _ = a[i], rfl : _ = i⟩ := h
    exact h
  rw [← this]
  apply (Prod.Lex.le_iff (y := (a[i], i))).mp
  exact Finset.inf'_le _ (Finset.mem_univ _)

lemma minIdx_le (a : Vector α n) (i : Fin n) :
    a[a.minIdx] ≤ a[i] :=
  (a.minIdx_spec i).elim LT.lt.le (fun ⟨h, _⟩ ↦ h.le)

end ReadOnly

instance WithDefault.instIndexedMinHeap [OrderTop α] :
    IndexedMinHeap (Vector.WithDefault α n fun _ ↦ ⊤) (Fin n) α where
  minIdx := minIdx
  getElem_minIdx_le a i := a.minIdx_le i

end Vector

namespace WithTop

instance (α) (x : WithTop α) : Decidable (x = ⊤) :=
  match x with
  | ⊤ => .isTrue rfl
  | (x : α) => .isFalse nofun

end WithTop

structure AssocArrayWithHeap.WithIdx (α ι : Type*) where
  val : α
  idx : ι

namespace AssocArrayWithHeap.WithIdx
variable {α ι : Type*}

instance [LE α] : LE (AssocArrayWithHeap.WithIdx α ι) where
  le x y := x.val ≤ y.val

lemma le_def [LE α] {x y : AssocArrayWithHeap.WithIdx α ι} :
    x ≤ y ↔ x.val ≤ y.val :=
  Iff.rfl

@[simp]
lemma mk_le_mk [LE α] {x y : α} {xi yi : ι} :
    mk x xi ≤ mk y yi ↔ x ≤ y :=
  Iff.rfl

instance [LT α] : LT (AssocArrayWithHeap.WithIdx α ι) where
  lt x y := x.val < y.val

@[simp]
lemma mk_lt_mk [LT α] {x y : α} {xi yi : ι} :
    mk x xi < mk y yi ↔ x < y :=
  Iff.rfl

instance [Preorder α] : Preorder (AssocArrayWithHeap.WithIdx α ι) where
  le_refl _ := le_refl _
  le_trans _ _ _ := le_trans
  lt_iff_le_not_ge _ _ := lt_iff_le_not_ge

instance [Preorder α] [IsTotal α (· ≤ ·)] :
    IsTotal (AssocArrayWithHeap.WithIdx α ι) (· ≤ ·) where
  total _ _ := total_of (α := α) (· ≤ ·) _ _

end AssocArrayWithHeap.WithIdx

structure AssocArrayWithHeap (C C' : Type*) {ι α : Type*} [Preorder α] [IsTotal α (· ≤ ·)]
    [Inhabited C] [AssocArray C ι (WithTop α) ⊤]
    [MinHeap C' (AssocArrayWithHeap.WithIdx α ι)] where mk' ::
  assocArray : C
  minHeap : C'
  mem_minHeap' : ∀ i : ι, (hi : assocArray[i] ≠ ⊤) → ⟨assocArray[i].untop hi, i⟩ ∈ minHeap
  getElem_minIdx' : (h : ¬isEmpty minHeap) →
    assocArray[(MinHeap.head minHeap h).idx] = (MinHeap.head minHeap h).val

namespace AssocArrayWithHeap
variable {C C' : Type*} {ι α : Type*} [Preorder α] [IsTotal α (· ≤ ·)]
  [Inhabited C] [AssocArray C ι (WithTop α) ⊤]
  [MinHeap C' (AssocArrayWithHeap.WithIdx α ι)]

instance : AssocArray.ReadOnly (AssocArrayWithHeap C C') ι (WithTop α) ⊤ where
  getElem c i _ := c.assocArray[i]
  toDFinsupp' c := toDFinsupp' c.assocArray
  coe_toDFinsupp'_eq_getElem c := coe_toDFinsupp'_eq_getElem c.assocArray

@[simp]
lemma assocArray_getElem (c : AssocArrayWithHeap C C') (i : ι) :
    c.assocArray[i] = c[i] :=
  rfl

lemma mem_minHeap (c : AssocArrayWithHeap C C') :
    ∀ i : ι, (hi : c[i] ≠ ⊤) → ⟨c[i].untop hi, i⟩ ∈ c.minHeap :=
  c.mem_minHeap'

lemma getElem_minIdx (c : AssocArrayWithHeap C C') (h : ¬isEmpty c.minHeap) :
    c[(MinHeap.head c.minHeap h).idx] = (MinHeap.head c.minHeap h).val :=
  c.getElem_minIdx' h

instance : Inhabited (AssocArrayWithHeap C C') where
  default := ⟨default, ∅, by simp, by simp [size_eq_card_toMultiset]⟩

def mk [DecidableEq α] (assocArray : C) (minHeap : C')
    (mem_minHeap : ∀ i : ι, (hi : assocArray[i] ≠ ⊤) → ⟨(assocArray[i]).untop hi, i⟩ ∈ minHeap) :
    AssocArrayWithHeap C C' :=
  if h : isEmpty minHeap then
    ⟨assocArray, minHeap, mem_minHeap, (False.elim <| · h)⟩
  else if h' : assocArray[(MinHeap.head minHeap h).idx] = (MinHeap.head minHeap h).val then
    ⟨assocArray, minHeap, mem_minHeap, fun _ ↦ h'⟩
  else
    haveI : DecidableEq (WithIdx α ι) := by classical infer_instance
    have : size (MinHeap.tail minHeap) < size minHeap := by
      simpa [h, size_eq_card_toMultiset, Multiset.card_erase_lt_of_mem] using
        Multiset.card_erase_lt_of_mem (MinHeap.head_mem_toMultiset _ _)
    mk assocArray (MinHeap.tail minHeap) fun i hi ↦ by
      simp only [← mem_toMultiset, MinHeap.toMultiset_tail, h, Bool.false_eq_true, ↓reduceDIte,
        MinHeap.head_def]
      rw [Multiset.mem_erase_of_ne, mem_toMultiset]
      · exact mem_minHeap _ _
      · intro h''
        apply h'
        simp [← h'', MinHeap.head_def]
termination_by size minHeap

@[simp, nolint unusedHavesSuffices] -- false positive
lemma mk_assocArray [DecidableEq α] (assocArray : C) (minHeap : C')
    (mem_minHeap : ∀ i : ι, (hi : assocArray[i] ≠ ⊤) → ⟨(assocArray[i]).untop hi, i⟩ ∈ minHeap) :
    (mk assocArray minHeap mem_minHeap).assocArray = assocArray := by
  induction minHeap, mem_minHeap using mk.induct
  all_goals unfold mk; simp [*]

@[simp]
lemma default_assocArray :
    (default : AssocArrayWithHeap C C').assocArray = default :=
  rfl

@[simp]
lemma default_minHeap :
    (default : AssocArrayWithHeap C C').minHeap = ∅ :=
  rfl

instance [DecidableEq α] :
    AssocArray (AssocArrayWithHeap C C') ι (WithTop α) ⊤ where
  setElem c i x :=
    mk
      c.assocArray[i ↦ x]
      (if hx : x = ⊤ then c.minHeap else insert ⟨x.untop hx, i⟩ c.minHeap)
      fun j hj ↦ by
        haveI : DecidableEq ι := by classical infer_instance
        split_ifs with hx <;>
          simp? [Function.update_apply] at hj ⊢ says
            simp only [all_valid, getElem_setElem, assocArray_getElem, ne_eq] at hj ⊢
        · subst hx
          rw [ite_eq_left_iff, Classical.not_imp] at hj
          simp only [hj.1, ↓reduceIte]
          exact c.mem_minHeap j hj.2
        · -- TODO: `mem_insert`
          rw [← mem_toMultiset, toMultiset_insert, Multiset.mem_cons, mem_toMultiset]
          split_ifs at hj ⊢ with hji
          · simp [hji]
          · exact .inr <| c.mem_minHeap j hj
  getElem_setElem_self _ _ _ := by simp [getElem]
  getElem_setElem_of_ne _ _ _ _ _ := by simp only [getElem]; simp [*]
  getElem_default := by simp [getElem]

@[simp]
lemma set_assocArray [DecidableEq α] (c : AssocArrayWithHeap C C') (i : ι) (x) :
    c[i ↦ x].assocArray = c.assocArray[i ↦ x] := by
  unfold_projs; simp

instance [Inhabited ι] [DecidableEq α] :
    IndexedMinHeap (AssocArrayWithHeap C C') ι (WithTop α) where
  minIdx c := if h : isEmpty c.minHeap then default else (MinHeap.head c.minHeap h).idx
  getElem_minIdx_le c i := by
    split_ifs with h
    · suffices ∀ i : ι, c[i] = ⊤ by simp [this]
      intro i
      contrapose h with hi
      simpa [size_eq_card_toMultiset, Multiset.eq_zero_iff_forall_notMem] using
        ⟨_, c.mem_minHeap i hi⟩
    · rw [getElem_minIdx c h, WithTop.coe_le_iff]
      intro x hx
      refine (WithIdx.le_def.mp <| MinHeap.head_le c.minHeap _ (c.mem_minHeap i ?_)).trans ?_ <;>
        simp [hx]
  -- 我们不能定义一个无需操作堆的 `decreaseKey`，除非假设 `LinearOrder`。
  -- 考虑有无法通过比较区分的 `x` 和 `x'`， `fun | 0 ↦ x + 1 | 1 ↦ x'`
  -- 堆中按顺序为 `(x', 1)` `(x, 0)` `(x + 1, 0)`
  -- 将 `0` 处更新为 `x'`，堆可以变为 `(x, 0)` `(x', 0)` `(x', 1)` `(x + 1, 0)`
  -- 此时必须操作堆弹出 `(x, 0)`
  -- decreaseKey c i x hx := ⟨AssocArray.set c.assocArray i x,
  --   insert ⟨x.untop (hx.trans_le le_top).ne, i⟩ c.minHeap,
  --   by
  --     haveI : DecidableEq ι := by classical infer_instance
  --     intro j hj
  --     simp? [Function.update_apply] at hj ⊢ says
  --       simp only [AssocDArray.getElem_set, Function.update_apply, AssocDArray.get_eq_getElem,
  --         assocArray_getElem, ne_eq] at hj ⊢
  --     rw [ToMultiset.mem_iff, toMultiset_insert, Multiset.mem_cons]
  --     split_ifs at hj ⊢ with hji
  --     · simp [hji]
  --     · exact .inr <| c.mem_minHeap j hj,

end AssocArrayWithHeap
