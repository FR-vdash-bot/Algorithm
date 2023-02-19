
import Algorithm.Data.Classes.AssocArray
import Mathlib.Data.List.Nodup

structure Graph where
  V : Type _
  [decidableEqV : DecidableEq V]
  EType : Type _
  fst' : EType → V
  snd' : EType → V
  StarList : Type _
  [assocArrayStarList : AssocArray V (List EType) StarList]
  star' : StarList
  costar' : StarList
  fst_star' : ∀ v, ∀ e ∈ AssocArray.get star' v, fst' e = v
  snd_costar' : ∀ v, ∀ e ∈ AssocArray.get costar' v, snd' e = v
  nodup_star' : ∀ v, (AssocArray.get star' v).Nodup
  nodup_costar' : ∀ v, (AssocArray.get costar' v).Nodup
  mem_star'_iff_mem_costar' : ∀ e,
    e ∈ AssocArray.get star' (fst' e) ↔ e ∈ AssocArray.get costar' (snd' e)

namespace Graph

attribute [instance] decidableEqV assocArrayStarList

variable {g : Graph}
-- instance : GetElem g.StarList g.V (List g.E) (fun _ _ ↦ True) := AssocArray.instGetElem
-- by infer_instance

def EType.fst (e : g.EType) : g.V := g.fst' e
def EType.snd (e : g.EType) : g.V := g.snd' e

def V.star (v : g.V) : List g.EType := AssocArray.get g.star' v
def V.costar (v : g.V) : List g.EType := AssocArray.get g.costar' v

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
