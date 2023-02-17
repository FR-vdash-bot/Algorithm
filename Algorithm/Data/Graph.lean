
import Algorithm.Data.Classes.AssocArray

structure Graph where
  V : Type _
  [instDecidableEqV : DecidableEq V]
  E : Type _
  fst' : E → V
  snd' : E → V
  StarList : Type _
  [instAssocArrayStarList : AssocArray V (List E) StarList]
  star' : StarList
  costar' : StarList
  fst_star' : ∀ v, ∀ e ∈ AssocArray.get star' v, fst' e = v
  snd_costar' : ∀ v, ∀ e ∈ AssocArray.get costar' v, snd' e = v

namespace Graph
variable {g : Graph}

instance : DecidableEq g.V := g.instDecidableEqV
instance : AssocArray g.V (List g.E) g.StarList := g.instAssocArrayStarList
-- instance : GetElem g.StarList g.V (List g.E) (fun _ _ ↦ True) := AssocArray.instGetElem
-- by infer_instance

def E.fst (e : g.E) : g.V := g.fst' e
def E.snd (e : g.E) : g.V := g.snd' e

def V.star (v : g.V) : List g.E := AssocArray.get g.star' v
def V.costar (v : g.V) : List g.E := AssocArray.get g.costar' v

lemma fst_star (v : g.V) : ∀ e ∈ v.star, e.fst = v := g.fst_star' v
lemma snd_costar (v : g.V) : ∀ e ∈ v.costar, e.snd = v := g.snd_costar' v

end Graph
