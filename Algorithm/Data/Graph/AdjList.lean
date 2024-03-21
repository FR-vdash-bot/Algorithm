
import Algorithm.Data.Classes.AssocArray
import Algorithm.Data.Classes.Collection
-- import Mathlib.Data.List.Nodup
import Mathlib.Combinatorics.Quiver.Path

structure AdjList
    (V : Type*) [DecidableEq V]
    (EType : Type*) [DecidableEq EType]
    (EColl : Type*) [Collection EColl EType] [Inhabited EColl]
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

variable
  {V : Type*} [DecidableEq V]
  {EType : Type*} [DecidableEq EType]
  {EColl : Type*} [Collection EColl EType] [Inhabited EColl]
  {StarList : Type*} [AssocArray StarList V EColl] {g : AdjList V EType EColl StarList}
-- instance : GetElem g.StarList g.V (List g.E) (fun _ _ ↦ True) := AssocArray.instGetElem
-- by infer_instance

-- lemma nodup_star (v : g.V) : v.star.Nodup := g.nodup_star' v
-- lemma nodup_costar (v : g.V) : v.costar.Nodup := g.nodup_costar' v

lemma mem_star_iff_mem_costar (e : EType) : e ∈ g.star[g.fst e] ↔ e ∈ g.costar[g.snd e] := by
  rw [← countSlow_ne_zero, ← countSlow_ne_zero,
    countSlow_star_fst_eq_countSlow_costar_snd]

@[pp_dot]
def E (g : AdjList V EType EColl StarList) := {e : EType // e ∈ g.star[g.fst e]}

@[pp_dot]
def val (e : g.E) : EType := e.val

@[pp_dot]
def E.fst (e : g.E) : V := g.fst e.val

@[pp_dot]
def E.snd (e : g.E) : V := g.snd e.val

@[simp]
lemma E.fst_val (e : g.E) : g.fst e.val = e.fst := rfl

@[simp]
lemma E.snd_val (e : g.E) : g.snd e.val = e.snd := rfl

lemma E.mem_star (e : g.E) : e.val ∈ g.star[e.fst] := e.2
lemma E.mem_costar (e : g.E) : e.val ∈ g.costar[e.snd] := (mem_star_iff_mem_costar _).mp e.2

set_option linter.unusedVariables false in
@[pp_dot]
protected def Quiver (g : AdjList V EType EColl StarList) : Type _ := V

@[pp_dot]
def toQuiver (g : AdjList V EType EColl StarList) : V ≃ g.Quiver := Equiv.refl _

@[pp_dot]
def ofQuiver (g : AdjList V EType EColl StarList) : g.Quiver ≃ V := Equiv.refl _

@[simp]
lemma toQuiver_ofQuiver (g : AdjList V EType EColl StarList) (v : g.Quiver) :
    g.toQuiver (g.ofQuiver v) = v :=
  rfl

@[simp]
lemma ofQuiver_toQuiver (g : AdjList V EType EColl StarList) (v : V) :
    g.ofQuiver (g.toQuiver v) = v :=
  rfl

instance : Quiver g.Quiver where
  Hom v w := {e : g.E // g.toQuiver e.fst = v ∧ g.toQuiver e.snd = w}

@[pp_dot]
def toHom (g : AdjList V EType EColl StarList) (e : g.E) :
    g.toQuiver e.fst ⟶ g.toQuiver e.snd :=
  ⟨e, ⟨rfl, rfl⟩⟩

@[pp_dot]
def ofHom (g : AdjList V EType EColl StarList) {v w : g.Quiver} (e : v ⟶ w) :
    g.E :=
  e.1

@[simp]
lemma ofHom_fst (g : AdjList V EType EColl StarList) {v w : g.Quiver}
    (e : v ⟶ w) :
    (g.ofHom e).fst = g.ofQuiver v :=
  e.2.1

@[simp]
lemma ofHom_snd (g : AdjList V EType EColl StarList) {v w : g.Quiver}
    (e : v ⟶ w) :
    (g.ofHom e).snd = g.ofQuiver w :=
  e.2.2

end AdjList
