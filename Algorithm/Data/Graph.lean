
import Algorithm.Data.Classes.AssocArray
import Mathlib.Data.List.Nodup

structure Graph where
  V : Type _
  [decidableEqV : DecidableEq V]
  EType : Type _
  fst' : EType → V
  snd' : EType → V
  StarList : Type _
  [assocArrayStarList : AssocArray StarList V (List EType)]
  star' : StarList
  costar' : StarList
  fst_star' : ∀ v, ∀ e ∈ star'[v], fst' e = v
  snd_costar' : ∀ v, ∀ e ∈ costar'[v], snd' e = v
  nodup_star' : ∀ v : V, star'[v].Nodup
  nodup_costar' : ∀ v : V, costar'[v].Nodup
  mem_star'_iff_mem_costar' : ∀ e, e ∈ star'[fst' e] ↔ e ∈ costar'[snd' e]

namespace Graph

attribute [instance] decidableEqV assocArrayStarList

variable {g : Graph}
-- instance : GetElem g.StarList g.V (List g.E) (fun _ _ ↦ True) := AssocArray.instGetElem
-- by infer_instance

def EType.fst (e : g.EType) : g.V := g.fst' e
def EType.snd (e : g.EType) : g.V := g.snd' e

def V.star (v : g.V) : List g.EType := g.star'[v]
def V.costar (v : g.V) : List g.EType := g.costar'[v]

lemma fst_star (v : g.V) : ∀ e ∈ v.star, e.fst = v := g.fst_star' v
lemma snd_costar (v : g.V) : ∀ e ∈ v.costar, e.snd = v := g.snd_costar' v

lemma nodup_star (v : g.V) : v.star.Nodup := g.nodup_star' v
lemma nodup_costar (v : g.V) : v.costar.Nodup := g.nodup_costar' v

lemma mem_star_iff_mem_costar (e : g.EType) : e ∈ e.fst.star ↔ e ∈ e.snd.costar :=
  g.mem_star'_iff_mem_costar' e

def E (g : Graph) := {e : g.EType // e ∈ e.fst.star}

def E.fst (e : g.E) : g.V := e.val.fst
def E.snd (e : g.E) : g.V := e.val.snd

lemma E.mem_star (e : g.E) : e.val ∈ e.fst.star := e.2
lemma E.mem_costar (e : g.E) : e.val ∈ e.snd.costar := (mem_star_iff_mem_costar _).mp e.2

end Graph
