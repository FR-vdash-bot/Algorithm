
import Algorithm.Data.Classes.AssocArray
import Algorithm.Data.Classes.Collection
-- import Mathlib.Data.List.Nodup
-- import Mathlib.Combinatorics.Quiver.Path

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

def E (g : AdjList V EType EColl StarList) := {e : EType // e ∈ g.star[g.fst e]}

def E.fst (e : g.E) : V := g.fst e.val
def E.snd (e : g.E) : V := g.snd e.val

lemma E.mem_star (e : g.E) : e.val ∈ g.star[e.fst] := e.2
lemma E.mem_costar (e : g.E) : e.val ∈ g.costar[e.snd] := (mem_star_iff_mem_costar _).mp e.2

protected def Quiver : Type _ := V

end AdjList
