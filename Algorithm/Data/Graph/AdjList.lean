
import Algorithm.Data.Classes.AssocArray
import Algorithm.Data.Classes.ToList
-- import Mathlib.Data.List.Nodup
import Mathlib.Combinatorics.Quiver.Path

structure AdjList
    (V : Type*) [DecidableEq V]
    (EType : Type*) [DecidableEq EType]
    (EColl : Type*) [ToMultiset EColl EType] [Inhabited EColl]
    (StarList : Type*) [AssocArray StarList V EColl] where
  fst : EType → V
  snd : EType → V
  star : StarList
  costar : StarList
  fst_star v : ∀ e ∈ star[v], fst e = v
  snd_costar v : ∀ e ∈ costar[v], snd e = v
  countSlow_star_fst_eq_countSlow_costar_snd e :
    countSlow e star[fst e] = countSlow e costar[snd e]
  -- nodup_star' (v : V) : star'[v].Nodup
  -- nodup_costar' (v : V) : costar'[v].Nodup
  -- mem_star'_iff_mem_costar' e : e ∈ star'[fst' e] ↔ e ∈ costar'[snd' e]

namespace AdjList

attribute [pp_dot] fst snd star costar

section ToMultiset
variable
  {V : Type*} [DecidableEq V]
  {EType : Type*} [DecidableEq EType]
  {EColl : Type*} [ToMultiset EColl EType] [Inhabited EColl]
  {StarList : Type*} [AssocArray StarList V EColl] {g : AdjList V EType EColl StarList}
-- instance : GetElem g.StarList g.V (List g.E) (fun _ _ ↦ True) := AssocArray.instGetElem
-- by infer_instance

-- lemma nodup_star (v : g.V) : v.star.Nodup := g.nodup_star' v
-- lemma nodup_costar (v : g.V) : v.costar.Nodup := g.nodup_costar' v

lemma mem_star_iff_mem_costar (e : EType) : e ∈ g.star[g.fst e] ↔ e ∈ g.costar[g.snd e] := by
  rw [← countSlow_ne_zero, ← countSlow_ne_zero,
    countSlow_star_fst_eq_countSlow_costar_snd]

variable (g) in
@[pp_dot]
def E := {e : EType // e ∈ g.star[g.fst e]}

@[pp_dot]
def E.val (e : g.E) : EType := Subtype.val e

def starToE (v : V) (e : EType) (he : e ∈ g.star[v]) : g.E :=
  ⟨e, g.fst_star v e he ▸ he⟩

def costarToE (v : V) (e : EType) (he : e ∈ g.costar[v]) : g.E :=
  ⟨e, (g.mem_star_iff_mem_costar e).mpr <| g.snd_costar v e he ▸ he⟩

@[pp_dot]
def E.fst (e : g.E) : V := g.fst e.val

@[pp_dot]
def E.snd (e : g.E) : V := g.snd e.val

@[simp]
lemma E.fst_val (e : g.E) : g.fst e.val = e.fst := rfl

@[simp]
lemma starToE_fst (v : V) (e : EType) (he : e ∈ g.star[v]) :
    (g.starToE v e he).fst = v :=
  g.fst_star v e he

@[simp]
lemma costarToE_snd (v : V) (e : EType) (he : e ∈ g.costar[v]) :
    (g.costarToE v e he).snd = v :=
  g.snd_costar v e he

@[simp]
lemma E.snd_val (e : g.E) : g.snd e.val = e.snd := rfl

lemma E.mem_star (e : g.E) : e.val ∈ g.star[e.fst] := e.2
lemma E.mem_costar (e : g.E) : e.val ∈ g.costar[e.snd] := (mem_star_iff_mem_costar _).mp e.2

@[pp_dot]
protected structure Quiver (g : AdjList V EType EColl StarList) where
  _intro ::
  val : V

attribute [coe] Quiver.val

instance : CoeOut g.Quiver V := ⟨Quiver.val⟩

section Quiver

variable (g) in
@[pp_dot]
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

instance : Quiver g.Quiver where
  Hom v w := {e : g.E // g.toQuiver e.fst = v ∧ g.toQuiver e.snd = w}

@[pp_dot]
def E.toHom (e : g.E) :
    g.toQuiver e.fst ⟶ g.toQuiver e.snd :=
  ⟨e, ⟨rfl, rfl⟩⟩

@[pp_dot]
def ofHom {v w : g.Quiver} (e : v ⟶ w) :
    g.E :=
  e.1

@[simp]
lemma ofHom_fst {v w : g.Quiver}
    (e : v ⟶ w) :
    (g.ofHom e).fst = ↑v :=
  congr_arg Quiver.val e.2.1

@[simp]
lemma ofHom_snd {v w : g.Quiver}
    (e : v ⟶ w) :
    (g.ofHom e).snd = ↑w :=
  congr_arg Quiver.val e.2.2

@[pp_dot]
def ofStar (v : V) (e : EType) (he : e ∈ g.star[v]) :
    g.toQuiver v ⟶ g.toQuiver (g.snd e) :=
  ⟨starToE v e he, ⟨congr_arg g.toQuiver <| starToE_fst v e he, rfl⟩⟩

@[pp_dot]
def ofCostar (v : V) (e : EType) (he : e ∈ g.costar[v]) :
    g.toQuiver (g.fst e) ⟶ g.toQuiver v :=
  ⟨costarToE v e he, ⟨rfl, congr_arg g.toQuiver <| costarToE_snd v e he⟩⟩

end Quiver

variable (g) in
@[pp_dot]
def Adj (v w : V) : Prop := Nonempty (g.toQuiver v ⟶ g.toQuiver w)

variable (g) in
@[pp_dot]
def Reachable (v w : V) : Prop := Nonempty (Quiver.Path (g.toQuiver v) (g.toQuiver w))

namespace Adj

lemma of_star {v : V} (e : EType) (he : e ∈ g.star[v]) :
    g.Adj v (g.snd e) :=
  ⟨ofStar v e he⟩

lemma of_costar {v : V} (e : EType) (he : e ∈ g.costar[v]) :
    g.Adj (g.fst e) v :=
  ⟨ofCostar v e he⟩

lemma to_reachable {v w : V} (h : g.Adj v w) :
    g.Reachable v w :=
  h.map (·.toPath)

end Adj

namespace Reachable

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

variable (g) in
@[pp_dot]
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

end lemmas

end ToMultiset

section ToList
variable
  {V : Type*} [DecidableEq V]
  {EType : Type*} [DecidableEq EType]
  {EColl : Type*} [ToList EColl EType] [Inhabited EColl]
  {StarList : Type*} [AssocArray StarList V EColl]
  (g : AdjList V EType EColl StarList)

@[pp_dot]
def succList (v : V) : List V := (toList g.star[v]).map g.snd

-- @[pp_dot]
-- def succSet (s : Set V) : Set V := ⋃ v ∈ s, {t | t ∈ g.succList v}

-- section lemmas
-- variable {g}

-- @[simp]
-- lemma mem_succList_iff {v w : V} : w ∈ g.succList v ↔ ∃ e ∈ g.star[v], g.snd e = w :=
--   List.mem_map

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
