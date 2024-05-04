/-
Copyright (c) 2023 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Algorithm.Data.Classes.AssocArray
import Algorithm.Data.Classes.ToList
-- import Mathlib.Data.List.Nodup
import Mathlib.Combinatorics.Quiver.Path

structure AdjList
    (V : Type*) (EType : Type*)
    (EColl : Type*) [ToMultiset EColl EType] [Inhabited EColl]
    (StarColl : Type*) [AssocArray.ReadOnly StarColl V EColl] where
  fst : EType → V
  snd : EType → V
  star : StarColl
  costar : StarColl
  fst_star' v : ∀ e ∈ star[v], fst e = v
  snd_costar' v : ∀ e ∈ costar[v], snd e = v
  count_star_fst_eq_count_costar_snd : [DecidableEq EType] → ∀ e,
    (toMultiset star[fst e]).count e = (toMultiset costar[snd e]).count e
  -- nodup_star' (v : V) : star'[v].Nodup
  -- nodup_costar' (v : V) : costar'[v].Nodup
  -- mem_star'_iff_mem_costar' e : e ∈ star'[fst' e] ↔ e ∈ costar'[snd' e]

namespace AdjList

section ToMultiset
variable
  {V : Type*} {EType : Type*}
  {EColl : Type*} [ToMultiset EColl EType] [Inhabited EColl]
  {StarColl : Type*} [AssocArray.ReadOnly StarColl V EColl] {g : AdjList V EType EColl StarColl}
-- instance : GetElem g.StarColl g.V (List g.E) (fun _ _ ↦ True) := AssocArray.instGetElem
-- by infer_instance

lemma fst_star {v e} : e ∈ g.star[v] → g.fst e = v := g.fst_star' _ _
lemma snd_costar {v e} : e ∈ g.costar[v] → g.snd e = v := g.snd_costar' _ _

-- lemma nodup_star (v : g.V) : v.star.Nodup := g.nodup_star' v
-- lemma nodup_costar (v : g.V) : v.costar.Nodup := g.nodup_costar' v

lemma mem_star_iff_mem_costar {e : EType} : e ∈ g.star[g.fst e] ↔ e ∈ g.costar[g.snd e] := by
  classical rw [← count_toMultiset_ne_zero, ← count_toMultiset_ne_zero,
    count_star_fst_eq_count_costar_snd]

variable (g) in
def IsE (e : EType) : Prop := e ∈ g.star[g.fst e]

lemma IsE.mem_star {e : EType} : g.IsE e → e ∈ g.star[g.fst e] := id
lemma IsE.mem_costar {e : EType} : g.IsE e → e ∈ g.costar[g.snd e] := mem_star_iff_mem_costar.mp

lemma IsE.of_mem_star {e : EType} {v : V} (he : e ∈ g.star[v]) : g.IsE e :=
  show e ∈ g.star[g.fst e] by rwa [fst_star he]

lemma IsE.of_mem_costar {e : EType} {v : V} (he : e ∈ g.costar[v]) : g.IsE e :=
  mem_star_iff_mem_costar.mpr (by rwa [snd_costar he])

@[simp]
lemma mem_star_iff {e : EType} {v : V} : e ∈ g.star[v] ↔ g.IsE e ∧ g.fst e = v :=
  ⟨fun he ↦ ⟨.of_mem_star he, fst_star he⟩, fun ⟨he, hv⟩ ↦ hv ▸ he.mem_star⟩

@[simp]
lemma mem_costar_iff {e : EType} {v : V} : e ∈ g.costar[v] ↔ g.IsE e ∧ g.snd e = v :=
  ⟨fun he ↦ ⟨.of_mem_costar he, snd_costar he⟩, fun ⟨h₁, h₂⟩ ↦ h₂ ▸ h₁.mem_costar⟩

variable (g) in
def E := {e : EType // g.IsE e}

@[coe]
def E.val (e : g.E) : EType := Subtype.val e

instance : CoeOut g.E EType := ⟨E.val⟩

@[simp]
lemma E.isE_val (e : g.E) : g.IsE e := e.2

def starToE (e : EType) {v : V} (he : e ∈ g.star[v]) : g.E :=
  ⟨e, .of_mem_star he⟩

def costarToE (e : EType) {v : V} (he : e ∈ g.costar[v]) : g.E :=
  ⟨e, .of_mem_costar he⟩

def E.fst (e : g.E) : V := g.fst e.val

def E.snd (e : g.E) : V := g.snd e.val

@[simp]
lemma E.coe_mk (e : EType) (he : g.IsE e) : E.val ⟨e, he⟩ = e := rfl

@[simp]
theorem E.coe_inj {e₁ e₂ : g.E} : e₁.val = e₂.val ↔ e₁ = e₂ :=
  Subtype.coe_inj

@[simp]
lemma E.mk_fst (e : EType) (he : g.IsE e) : E.fst ⟨e, he⟩ = g.fst e := rfl

@[simp]
lemma E.mk_snd (e : EType) (he : g.IsE e) : E.snd ⟨e, he⟩ = g.snd e := rfl

@[simp]
lemma E.fst_val (e : g.E) : g.fst e.val = e.fst := rfl

@[simp]
lemma E.snd_val (e : g.E) : g.snd e.val = e.snd := rfl

@[simp]
lemma starToE_fst (v : V) (e : EType) (he : e ∈ g.star[v]) :
    (g.starToE e he).fst = v :=
  g.fst_star he

@[simp]
lemma costarToE_snd (v : V) (e : EType) (he : e ∈ g.costar[v]) :
    (g.costarToE e he).snd = v :=
  g.snd_costar he

lemma E.mem_star (e : g.E) : e.val ∈ g.star[e.fst] := e.2.mem_star
lemma E.mem_costar (e : g.E) : e.val ∈ g.costar[e.snd] := e.2.mem_costar

lemma E.mem_star_iff {e : g.E} {v : V} : e.val ∈ g.star[v] ↔ e.fst = v :=
  ⟨fun h ↦ fst_star h, fun h ↦ h ▸ mem_star e⟩

lemma E.mem_costar_iff {e : g.E} {v : V} : e.val ∈ g.costar[v] ↔ e.snd = v :=
  ⟨fun h ↦ snd_costar h, fun h ↦ h ▸ mem_costar e⟩

protected structure Quiver (g : AdjList V EType EColl StarColl) where
  _intro ::
  val : V

attribute [coe] Quiver.val

instance : CoeOut g.Quiver V := ⟨Quiver.val⟩

section Quiver

variable (g) in
def toQuiver : V ≃ g.Quiver := ⟨Quiver._intro, (↑), fun _ ↦ rfl, fun _ ↦ rfl⟩

@[simp]
lemma toQuiver_val (v : g.Quiver) :
    g.toQuiver ↑v = v :=
  rfl

variable (g) in
@[simp]
lemma val_toQuiver (v : V) :
    ↑(g.toQuiver v) = v :=
  rfl

-- 需要考虑相等的重边吗？
instance : Quiver g.Quiver where
  Hom v w := {e : g.E // g.toQuiver e.fst = v ∧ g.toQuiver e.snd = w}

-- instance {v w : g.Quiver} : CoeOut (v ⟶ w) g.E := ⟨Subtype.val⟩

def ofHom {v w : g.Quiver} (e : v ⟶ w) :
    g.E :=
  e.1

@[simp]
theorem ofHom_inj {v w : g.Quiver} {e₁ e₂ : v ⟶ w} : ofHom e₁ = ofHom e₂ ↔ e₁ = e₂ :=
  Subtype.coe_inj

instance [DecidableEq EType] {v w : g.Quiver} : DecidableEq (v ⟶ w) := fun e₁ e₂ ↦ by
  convert decEq (ofHom e₁).val (ofHom e₂).val
  simp

@[simp]
lemma mk_ofHom {v w : g.Quiver}
    (e : g.E) (he) :
    ofHom (⟨e, he⟩ : v ⟶ w) = e :=
  rfl

@[simp]
lemma ofHom_fst {v w : g.Quiver}
    (e : v ⟶ w) :
    (ofHom e).fst = ↑v :=
  congr_arg Quiver.val e.2.1

@[simp]
lemma ofHom_snd {v w : g.Quiver}
    (e : v ⟶ w) :
    (ofHom e).snd = ↑w :=
  congr_arg Quiver.val e.2.2

def homOfStar {v : V} (e : EType) (he : e ∈ g.star[v]) :
    g.toQuiver v ⟶ g.toQuiver (g.snd e) :=
  ⟨starToE e he, ⟨congr_arg g.toQuiver <| starToE_fst v e he, rfl⟩⟩

def homOfCostar {v : V} (e : EType) (he : e ∈ g.costar[v]) :
    g.toQuiver (g.fst e) ⟶ g.toQuiver v :=
  ⟨costarToE e he, ⟨rfl, congr_arg g.toQuiver <| costarToE_snd v e he⟩⟩

instance [DecidableEq V] [DecidableEq EType] {v w : g.Quiver} : Fintype (v ⟶ w) where
  elems :=
    (((toMultiset g.star[(v : V)]).filter (fun e ↦ g.snd e = (w : V))).pmap
      (fun e he ↦ by
        simp only [Multiset.mem_filter, mem_toMultiset, mem_star_iff] at he
        exact ⟨⟨e, he.1.1⟩, ⟨by simp [he.1.2], by simp [he.2]⟩⟩) (fun _ ↦ id)).toFinset
  complete := by
    rintro ⟨⟨e, he⟩, ⟨fste, snde⟩⟩
    simp only [E.mk_fst, E.mk_snd, Multiset.mem_toFinset, Multiset.mem_pmap, Multiset.mem_filter,
      mem_toMultiset, mem_star_iff] at fste snde ⊢
    subst fste snde
    use e
    simpa

end Quiver

variable (g) in
def Adj (v w : V) : Prop := Nonempty (g.toQuiver v ⟶ g.toQuiver w)

variable (g) in
def Reachable (v w : V) : Prop := Nonempty (Quiver.Path (g.toQuiver v) (g.toQuiver w))

namespace Adj

lemma of_star {v : V} (e : EType) (he : e ∈ g.star[v]) :
    g.Adj v (g.snd e) :=
  ⟨homOfStar e he⟩

lemma of_costar {v : V} (e : EType) (he : e ∈ g.costar[v]) :
    g.Adj (g.fst e) v :=
  ⟨homOfCostar e he⟩

lemma to_reachable {v w : V} (h : g.Adj v w) :
    g.Reachable v w :=
  h.map (·.toPath)

end Adj

@[simp]
lemma exists_iff_adj {v w : V} :
    (∃ e, g.IsE e ∧ g.fst e = v ∧ g.snd e = w) ↔ g.Adj v w :=
  ⟨fun ⟨e, he, h₁, h₂⟩ ↦ ⟨⟨e, he⟩, by simp [*]⟩, fun ⟨e⟩ ↦ ⟨ofHom e, by simp, by simp⟩⟩

@[simp]
lemma exists_iff_adj' {v w : V} :
    (∃ e, (g.IsE e ∧ g.fst e = v) ∧ g.snd e = w) ↔ g.Adj v w := by
  simp [and_assoc]

lemma adj_iff_star {v w : V} :
    g.Adj v w ↔ ∃ e ∈ g.star[v], g.snd e = w :=
  ⟨fun ⟨e⟩ ↦ ⟨(ofHom e).val, by simp, by simp⟩, fun ⟨e, he, h⟩ ↦ h ▸ .of_star e he⟩

lemma adj_iff_costar {v w : V} :
    g.Adj v w ↔ ∃ e ∈ g.costar[w], g.fst e = v :=
  ⟨fun ⟨e⟩ ↦ ⟨(ofHom e).val, by simp, by simp⟩, fun ⟨e, he, h⟩ ↦ h ▸ .of_costar e he⟩

namespace Reachable

lemma rfl {v : V} : g.Reachable v v := ⟨.nil⟩

variable (g) in
@[refl]
lemma refl (v : V) : g.Reachable v v := ⟨.nil⟩

instance : IsRefl V g.Reachable := ⟨refl g⟩

@[trans]
lemma trans {u v w : V} (huv : g.Reachable u v) (hvw : g.Reachable v w) :
    g.Reachable u w :=
  Nonempty.map2 .comp huv hvw

instance : IsTrans V g.Reachable := ⟨fun _ _ _ ↦ trans⟩

end Reachable

variable (g) in
lemma reachable_eq_reflTransGen : g.Reachable = Relation.ReflTransGen g.Adj := by
  ext v w
  constructor
  · intro ⟨h⟩
    rw [← g.val_toQuiver w]
    generalize g.toQuiver w = w' at *
    induction h with
    | nil => rfl
    | cons _ h ih => exact ih.tail ⟨h⟩
  · intro h
    induction h with
    | refl => rfl
    | tail _ h ih => exact ih.trans h.to_reachable

lemma Reachable.cases_head {v w : V} (hvw : g.Reachable v w) :
    v = w ∨ ∃ x, g.Adj v x ∧ g.Reachable x w := by
  rw [reachable_eq_reflTransGen] at hvw ⊢
  exact hvw.cases_head

variable (g) in
def ReachableWithin (s : Set V) (v w : V) : Prop :=
  Relation.ReflTransGen (fun v w ↦ g.Adj v w ∧ w ∈ s) v w

lemma ReachableWithin.mono {s t : Set V} {v w : V} (hst : s ⊆ t) (h : g.ReachableWithin s v w) :
    g.ReachableWithin t v w :=
  Relation.ReflTransGen.mono (fun _ _ ↦ And.imp_right (hst ·)) h

@[simp]
lemma reachableWithin_univ {v w : V} :
    g.ReachableWithin Set.univ v w ↔ g.Reachable v w := by
  rw [reachable_eq_reflTransGen]
  exact ⟨Relation.ReflTransGen.mono (by simp), Relation.ReflTransGen.mono (by simp)⟩

lemma ReachableWithin.cases_head {s : Set V} {v w : V} (h : g.ReachableWithin s v w) :
    v = w ∨ ∃ x, (g.Adj v x ∧ x ∈ s) ∧ g.ReachableWithin s x w :=
  Relation.ReflTransGen.cases_head h

lemma ReachableWithin.find {s : Set V} {v w : V}
    (h : g.ReachableWithin s v w) (t : Set V) :
    v ∉ s \ t ∧ g.ReachableWithin (s ∩ t) v w ∨ ∃ x ∈ s \ t, g.ReachableWithin (s ∩ t) x w := by
  induction h with
  | refl => if hv : v ∈ s \ t then exact .inr <| ⟨v, hv, .refl⟩ else exact .inl <| ⟨hv, .refl⟩
  | tail _p e ih =>
    rename_i w
    if hw : w ∈ t then
      obtain (⟨hv, p⟩ | ⟨x, hx, p⟩) := ih
      · exact .inl <| ⟨hv, p.tail ⟨e.1, e.2, hw⟩⟩
      · exact .inr <| ⟨x, hx, p.tail ⟨e.1, e.2, hw⟩⟩
    else
      exact .inr ⟨w, ⟨e.2, hw⟩, .refl⟩

lemma ReachableWithin.inter_compl_singleton_self {s : Set V} {v w : V}
    (h : g.ReachableWithin s v w) :
    g.ReachableWithin (s ∩ {v}ᶜ) v w := by
  obtain (⟨-, h⟩ | ⟨x, hx, h⟩) := h.find {v}ᶜ
  · exact h
  · simp only [sdiff_compl, Set.inf_eq_inter, Set.mem_inter_iff, Set.mem_compl_iff,
      Set.mem_singleton_iff] at hx
    exact hx.2 ▸ h

lemma reachableWithin_iff_inter_compl_singleton_self {s : Set V} {v w : V} :
    g.ReachableWithin s v w ↔ g.ReachableWithin (s ∩ {v}ᶜ) v w :=
  ⟨.inter_compl_singleton_self, .mono (Set.inter_subset_left _ _)⟩

variable (g) in
def succSet (s : Set V) : Set V := {w | ∃ v ∈ s, g.Adj v w} -- ⋃ v ∈ s, {w | g.Adj v w}

section lemmas

@[simp]
lemma mem_succSet_iff {s : Set V} {w : V} :
    w ∈ g.succSet s ↔ ∃ v ∈ s, g.Adj v w :=
  Iff.rfl

lemma mem_succSet_singleton_iff {v w : V} :
    w ∈ g.succSet {v} ↔ g.Adj v w := by
  simp

@[simp]
lemma succSet_empty :
    g.succSet ∅ = ∅ := by
  simp [succSet]

@[simp]
lemma succSet_union {s t : Set V} :
    g.succSet (s ∪ t) = g.succSet s ∪ g.succSet t := by
  simp [succSet, or_and_right, exists_or, Set.setOf_or]

variable (g) in
def traversal (s t : Set V) : Set V :=
  s ∪ {w | ∃ v ∈ t, g.ReachableWithin sᶜ v w}

lemma traversal_insert (s t : Set V) (v : V) (hv : v ∈ t) (t' : Set V)
    (hst : s ∩ t = ∅) (h : t' = (t ∪ g.succSet {v}) \ insert v s) :
    g.traversal (insert v s) t' = g.traversal s t := by
  ext w
  subst h
  constructor
  · rintro ((rfl | h) | h)
    · exact .inr ⟨w, hv, .refl⟩
    · exact .inl h
    · simp only [Set.mem_diff, Set.mem_union, mem_succSet_iff, Set.mem_singleton_iff,
        exists_eq_left, Set.mem_insert_iff, not_or, Set.mem_setOf_eq] at h
      obtain ⟨x, ⟨(hx | hx), hx'⟩, hxw⟩ := h
      · exact .inr ⟨x, hx, hxw.mono (Set.compl_subset_compl.mpr (Set.subset_insert _ _))⟩
      refine .inr ⟨v, hv, ?_⟩
      exact (hxw.mono (Set.compl_subset_compl.mpr (Set.subset_insert _ _))).head ⟨hx, hx'.2⟩
  · rintro (h | ⟨x, hx, h⟩)
    · exact .inl <| .inr h
    · obtain (⟨hxv, h⟩ | ⟨x, hxv, h⟩) := h.find {v}ᶜ
      · simp only [Set.eq_empty_iff_forall_not_mem, Set.mem_inter_iff, not_and'] at hst
        specialize hst _ hx
        simp only [sdiff_compl, Set.inf_eq_inter, Set.mem_inter_iff, Set.mem_compl_iff, hst,
          not_false_eq_true, Set.mem_singleton_iff, true_and] at hxv
        right
        simp only [← Set.union_singleton, Set.mem_diff, Set.mem_union, mem_succSet_iff,
          Set.mem_singleton_iff, exists_eq_left, not_or, Set.compl_union, Set.mem_setOf_eq]
        exact ⟨x, ⟨.inl hx, hst, hxv⟩, h⟩
      · simp only [sdiff_compl, Set.inf_eq_inter, Set.mem_inter_iff, Set.mem_compl_iff,
          Set.mem_singleton_iff] at hxv
        replace hxv := hxv.2; subst hxv
        obtain (rfl | ⟨y, hy, h⟩) := h.cases_head
        · exact Or.inl <| .inl rfl
        · simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_singleton_iff] at hy
          exact Or.inr ⟨y, ⟨.inr (by simp [hy]), by simp [hy]⟩, h.mono (fun _ h ↦ Or.rec h.2 h.1)⟩

end lemmas

end ToMultiset

section ToList
variable
  {V : Type*} {EType : Type*}
  {EColl : Type*} [ToList EColl EType] [Inhabited EColl]
  {StarColl : Type*} [AssocArray.ReadOnly StarColl V EColl]
  (g : AdjList V EType EColl StarColl)

def succList (v : V) : List V := (toList g.star[v]).map g.snd

@[simp]
lemma mem_succList_iff {v w : V} : w ∈ g.succList v ↔ g.Adj v w := by
  simp [succList, - mem_star_iff, ← adj_iff_star]

@[simp]
lemma succSet_singleton (v : V) : g.succSet {v} = {w | g.Adj v w} := by
  ext; simp

lemma succList_eq_succSet (v : V) : {w | w ∈ g.succList v} = g.succSet {v} := by
  simp

-- @[simp]
-- lemma mem_succSet_iff {s : Set V} {w : V} :
--     w ∈ g.succSet s ↔ ∃ v ∈ s, ∃ e ∈ g.star[v], g.snd e = w := by
--   simp [succSet]

-- lemma mem_succSet_singleton_iff {v w : V} :
--     w ∈ g.succSet {v} ↔ ∃ e ∈ g.star[v], g.snd e = w := by
--   simp

-- end lemmas

end ToList

end AdjList
