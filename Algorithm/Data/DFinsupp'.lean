
/-
Copyright (c) 2023 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.GroupTheory.GroupAction.BigOperators
import Mathlib.GroupTheory.Submonoid.Membership
import Mathlib.Data.Set.Finite
import Mathlib.Data.Finset.Preimage

/-!
Modified from `Mathlib.Data.DFinsupp.Basic`
-/


universe u u₁ u₂ v v₁ v₂ v₃ w x y l

open BigOperators

variable {ι : Type u} {γ : Type w} {β : ι → Type v} {β₁ : ι → Type v₁} {β₂ : ι → Type v₂}
variable {d : ∀ i, β i} {d₁ : ∀ i, β₁ i} {d₂ : ∀ i, β₂ i}
variable (β)

/-- A dependent function `Π i, β i` with finite support, with notation `Π₀' i, [β i, d i]`.

Note that `DFinsupp'.support` is the preferred API for accessing the support of the function,
`DFinsupp'.support'` is an implementation detail that aids computability; see the implementation
notes in this file for more information. -/
structure DFinsupp' (d : ∀ i, β i) : Type max u v where mk' ::
  /-- The underlying function of a dependent function with finite support (aka `DFinsupp'`). -/
  toFun : ∀ i, β i
  /-- The support of a dependent function with finite support (aka `DFinsupp'`). -/
  support' : Trunc { s : Multiset ι // ∀ i, i ∈ s ∨ toFun i = d i }

variable {β}

/--
`Π₀' i, [β i, d i]` denotes the type of dependent functions with finite support `DFinsupp β d`.
-/
notation3 "Π₀' "(...)", ""[" β:(scoped β => β) ", " d:(scoped d => d) "]" => DFinsupp' β d

namespace DFinsupp'

section Basic

instance instDFunLike : DFunLike (Π₀' i, [β i, d i]) ι β :=
  ⟨fun f => f.toFun, fun ⟨f₁, s₁⟩ ⟨f₂, s₁⟩ ↦ fun (h : f₁ = f₂) ↦ by
    subst h
    congr
    apply Subsingleton.elim ⟩

/-- Helper instance for when there are too many metavariables to apply `DFunLike.coeFunForall`
directly. -/
instance : CoeFun (Π₀' i, [β i, d i]) fun _ => ∀ i, β i :=
  inferInstance

@[simp]
theorem toFun_eq_coe (f : Π₀' i, [β i, d i]) : f.toFun = f :=
  rfl

@[ext]
theorem ext {f g : Π₀' i, [β i, d i]} (h : ∀ i, f i = g i) : f = g :=
  DFunLike.ext _ _ h

@[deprecated DFunLike.ext_iff]
theorem ext_iff {f g : Π₀' i, [β i, d i]} : f = g ↔ ∀ i, f i = g i :=
  DFunLike.ext_iff

lemma ne_iff {f g : Π₀' i, [β i, d i]} : f ≠ g ↔ ∃ i, f i ≠ g i := DFunLike.ne_iff

@[deprecated DFunLike.coe_injective]
theorem coeFn_injective : @Function.Injective (Π₀' i, [β i, d i]) (∀ i, β i) (⇑) :=
  DFunLike.coe_injective

instance : Inhabited (Π₀' i, [β i, d i]) :=
  ⟨⟨d, Trunc.mk <| ⟨∅, fun _ => Or.inr rfl⟩⟩⟩

@[simp, norm_cast] lemma coe_mk' (f : ∀ i, β i) (s) : ⇑(⟨f, s⟩ : Π₀' i, [β i, d i]) = f := rfl

@[simp, norm_cast] lemma coe_default : ⇑(default : Π₀' i, [β i, d i]) = d := rfl

theorem default_apply (i : ι) : (default : Π₀' i, [β i, d i]) i = d i :=
  rfl

/-- The composition of `f : ∀ i, β₁ i → β₂ i` and `g : Π₀' i, [β₁ i, d₁ i]` is
  `mapRange f hf g : Π₀ i, [β₂ i, d₂ i]`, well defined when `f i (d₁ i) = d₂ i`.
-/
def mapRange (f : ∀ i, β₁ i → β₂ i) (hf : ∀ i, f i (d₁ i) = d₂ i)
    (x : Π₀' i, [β₁ i, d₁ i]) : Π₀' i, [β₂ i, d₂ i] :=
  ⟨fun i => f i (x i),
    x.support'.map fun s => ⟨s.1, fun i => (s.2 i).imp_right fun h : x i = d₁ i => by
      rw [← hf i, ← h]⟩⟩

@[simp]
theorem mapRange_apply (f : ∀ i, β₁ i → β₂ i) (hf : ∀ i, f i (d₁ i) = d₂ i)
    (g : Π₀' i, [β₁ i, d₁ i]) (i : ι) : mapRange f hf g i = f i (g i) :=
  rfl

@[simp]
theorem mapRange_id (h : ∀ i, id (d₁ i) = d₁ i := fun i => rfl)
    (g : Π₀' i : ι, [β₁ i, d₁ i]) : mapRange (fun i => (id : β₁ i → β₁ i)) h g = g := by
  ext
  rfl

theorem mapRange_comp (f : ∀ i, β₁ i → β₂ i) (f₂ : ∀ i, β i → β₁ i)
    (hf : ∀ i, f i (d₁ i) = d₂ i) (hf₂ : ∀ i, f₂ i (d i) = d₁ i)
    (h : ∀ i, (f i ∘ f₂ i) (d i) = d₂ i) (g : Π₀' i : ι, [β i, d i]) :
    mapRange (fun i => f i ∘ f₂ i) h g = mapRange f hf (mapRange f₂ hf₂ g) := by
  ext
  simp only [mapRange_apply]; rfl

@[simp]
theorem mapRange_default (f : ∀ i, β₁ i → β₂ i) (hf : ∀ i, f i (d₁ i) = d₂ i) :
    mapRange f hf (default : Π₀' i, [β₁ i, d₁ i]) = d₂ := by
  ext
  simp only [mapRange_apply, coe_default, hf]

/-- Let `f i` be a binary operation `β₁ i → β₂ i → β i` such that `f i (d₁ i) (d₂ i) = d i`.
Then `zipWith f hf` is a binary operation
`Π₀' i, [β₁ i, d₁ i] → Π₀' i, [β₂ i, d₂ i] → Π₀' i, [β i, d i]`. -/
def zipWith (f : ∀ i, β₁ i → β₂ i → β i) (hf : ∀ i, f i (d₁ i) (d₂ i) = d i)
    (x : Π₀' i, [β₁ i, d₁ i]) (y : Π₀' i, [β₂ i, d₂ i]) :
    Π₀' i, [β i, d i] :=
  ⟨fun i => f i (x i) (y i), by
    refine' x.support'.bind fun xs => _
    refine' y.support'.map fun ys => _
    refine' ⟨xs + ys, fun i => _⟩
    obtain h1 | (h1 : x i = d₁ i) := xs.prop i
    · left
      rw [Multiset.mem_add]
      left
      exact h1
    obtain h2 | (h2 : y i = d₂ i) := ys.prop i
    · left
      rw [Multiset.mem_add]
      right
      exact h2
    right; rw [← hf, ← h1, ← h2]⟩

@[simp]
theorem zipWith_apply (f : ∀ i, β₁ i → β₂ i → β i) (hf : ∀ i, f i (d₁ i) (d₂ i) = d i)
    (g₁ : Π₀' i, [β₁ i, d₁ i])
    (g₂ : Π₀' i, [β₂ i, d₂ i]) (i : ι) : zipWith f hf g₁ g₂ i = f i (g₁ i) (g₂ i) :=
  rfl

@[simp]
theorem zipWith_default_left (f : ∀ i, β i → β i → β i)
    (hf : ∀ i x, f i (d i) x = x) (x : Π₀' i, [β i, d i]) :
    zipWith f (fun i ↦ hf _ _) default x = x := by
  ext
  simp [hf]

@[simp]
theorem zipWith_default_right (f : ∀ i, β i → β i → β i)
    (hf : ∀ i x, f i x (d i) = x) (x : Π₀' i, [β i, d i]) :
    zipWith f (fun i ↦ hf _ _) x default = x := by
  ext
  simp [hf]

@[simp]
theorem zipWith_swap (f : ∀ i, β₁ i → β₂ i → β i) (hf : ∀ i, f i (d₁ i) (d₂ i) = d i)
    (x : Π₀' i, [β₂ i, d₂ i]) (y : Π₀' i, [β₁ i, d₁ i]) :
    zipWith (fun i x y ↦ f i y x) hf x y = zipWith f hf y x := by
  ext; rfl

section Piecewise

variable (x y : Π₀' i, [β i, d i]) (s : Set ι) [∀ i, Decidable (i ∈ s)]

/-- `x.piecewise y s` is the finitely supported function equal to `x` on the set `s`,
  and to `y` on its complement. -/
def piecewise : Π₀' i, [β i, d i] :=
  zipWith (fun i x y => if i ∈ s then x else y) (fun i => ite_self (d i)) x y

theorem piecewise_apply (i : ι) : x.piecewise y s i = if i ∈ s then x i else y i :=
  zipWith_apply _ _ x y i

@[simp, norm_cast]
theorem coe_piecewise : ⇑(x.piecewise y s) = s.piecewise x y := by
  ext
  apply piecewise_apply

end Piecewise

end Basic

section FilterAndSubtypeDomain

/-- `filter p f` is the function which is `f i` if `p i` is true and `d i` otherwise. -/
def filter (p : ι → Prop) [DecidablePred p] (x : Π₀' i, [β i, d i]) : Π₀' i, [β i, d i] :=
  ⟨fun i => if p i then x i else d i,
    x.support'.map fun xs =>
      ⟨xs.1, fun i => (xs.prop i).imp_right fun H : x i = d i => by simp only [H, ite_self]⟩⟩

@[simp]
theorem filter_apply (p : ι → Prop) [DecidablePred p] (i : ι) (f : Π₀' i, [β i, d i]) :
    f.filter p i = if p i then f i else d i :=
  rfl

theorem filter_apply_pos {p : ι → Prop} [DecidablePred p] (f : Π₀' i, [β i, d i]) {i : ι}
    (h : p i) : f.filter p i = f i := by simp only [filter_apply, if_pos h]

theorem filter_apply_neg {p : ι → Prop} [DecidablePred p] (f : Π₀' i, [β i, d i]) {i : ι}
    (h : ¬p i) : f.filter p i = d i := by simp only [filter_apply, if_neg h]

@[simp]
theorem filter_default (p : ι → Prop) [DecidablePred p] :
    (default : Π₀' i, [β i, d i]).filter p = d := by
  ext
  simp

/-- `subtypeDomain p f` is the restriction of the finitely supported function
  `f` to the subtype `p`. -/
def subtypeDomain (p : ι → Prop) [DecidablePred p] (x : Π₀' i, [β i, d i]) :
    Π₀' i : Subtype p, [β i, d i] :=
  ⟨fun i => x (i : ι),
    x.support'.map fun xs =>
      ⟨(Multiset.filter p xs.1).attach.map fun j => ⟨j.1, (Multiset.mem_filter.1 j.2).2⟩, fun i =>
        (xs.prop i).imp_left fun H =>
          Multiset.mem_map.2
            ⟨⟨i, Multiset.mem_filter.2 ⟨H, i.2⟩⟩, Multiset.mem_attach _ _, Subtype.eta _ _⟩⟩⟩

@[simp]
theorem subtypeDomain_default {p : ι → Prop} [DecidablePred p] :
    subtypeDomain p (default : Π₀' i, [β i, d i]) = Subtype.restrict p d :=
  rfl

@[simp]
theorem subtypeDomain_apply {p : ι → Prop} [DecidablePred p] {i : Subtype p}
    {v : Π₀' i, [β i, d i]} : (subtypeDomain p v) i = v i :=
  rfl

end FilterAndSubtypeDomain

variable [DecidableEq ι]

section Basic

theorem finite_support (f : Π₀' i, [β i, d i]) : Set.Finite { i | f i ≠ d i } :=
  Trunc.induction_on f.support' fun xs ↦
    xs.1.finite_toSet.subset fun i H ↦ ((xs.prop i).resolve_right H)

variable (d) in
/-- Create an element of `Π₀' i, [β i, d i]` from a finset `s` and a function `x`
defined on this `Finset`. -/
def mk (s : Finset ι) (x : ∀ i : (↑s : Set ι), β (i : ι)) : Π₀' i, [β i, d i] :=
  ⟨fun i => if H : i ∈ s then x ⟨i, H⟩ else d i,
    Trunc.mk ⟨s.1, fun i => if H : i ∈ s then Or.inl H else Or.inr <| dif_neg H⟩⟩

variable {s : Finset ι} {x : ∀ i : (↑s : Set ι), β i} {i : ι}

@[simp]
theorem mk_apply : (mk d s x : ∀ i, β i) i = if H : i ∈ s then x ⟨i, H⟩ else d i :=
  rfl

theorem mk_of_mem (hi : i ∈ s) : (mk d s x : ∀ i, β i) i = x ⟨i, hi⟩ :=
  dif_pos hi

theorem mk_of_not_mem (hi : i ∉ s) : (mk d s x : ∀ i, β i) i = d i :=
  dif_neg hi

variable (d) in
theorem mk_injective (s : Finset ι) : Function.Injective (@mk ι β d _ s) := by
  intro x y H
  ext i
  have h1 : (mk d s x : ∀ i, β i) i = (mk d s y : ∀ i, β i) i := by rw [H]
  obtain ⟨i, hi : i ∈ s⟩ := i
  dsimp only [mk_apply, Subtype.coe_mk] at h1
  simpa only [dif_pos hi] using h1

instance unique [∀ i, Subsingleton (β i)] : Unique (Π₀' i, [β i, d i]) :=
  DFunLike.coe_injective.unique

instance uniqueOfIsEmpty [IsEmpty ι] : Unique (Π₀' i, [β i, d i]) :=
  DFunLike.coe_injective.unique

/-- Given `Fintype ι`, `equivFunOnFintype` is the `Equiv` between `Π₀' i, [β i, d i]` and
  `Π i, β i`. (All dependent functions on a finite type are finitely supported.) -/
@[simps apply]
def equivFunOnFintype [Fintype ι] : (Π₀' i, [β i, d i]) ≃ ∀ i, β i
    where
  toFun := (⇑)
  invFun f := ⟨f, Trunc.mk ⟨Finset.univ.1, fun _ => Or.inl <| Finset.mem_univ_val _⟩⟩
  left_inv _ := DFunLike.coe_injective rfl
  right_inv _ := rfl

@[simp]
theorem equivFunOnFintype_symm_coe [Fintype ι] (f : Π₀' i, [β i, d i]) :
    equivFunOnFintype.symm f = f :=
  Equiv.symm_apply_apply _ _

variable (d) in
/-- The function `single i b : Π₀' i, [β i, d i]` sends `i` to `b`
and all other points to `d i`. -/
def single (i : ι) (b : β i) : Π₀' i, [β i, d i] :=
  ⟨Function.update d i b, Trunc.mk
    ⟨{i}, fun j => (Decidable.eq_or_ne j i).imp (by simp) fun h => Function.update_noteq h _ _⟩⟩

theorem single_eq_functionUpdate {i b} : ⇑(single d i b) = Function.update d i b :=
  rfl

@[simp]
theorem single_apply {i i' b} :
    (single d i b : Π₀' i, [β i, d i]) i' = if h : i = i' then Eq.recOn h b else d i' := by
  rw [single_eq_functionUpdate, Function.update]
  simp [@eq_comm _ i i']

@[simp]
theorem single_eq_self (i) : single d i (d i) = default :=
  DFunLike.coe_injective <| Function.update_eq_self _ _

-- @[simp] -- Porting note (#10618): simp can prove this
theorem single_eq_same {i b} : single d i b i = b := by
  simp only [single_apply, dite_eq_ite, ite_true]

theorem single_eq_of_ne {i i' b} (h : i ≠ i') : single d i b i' = d i' := by
  simp only [single_apply, dif_neg h]

theorem single_injective {i} : Function.Injective (single d i) := fun _ _ H =>
  Function.update_injective _ i <| DFunLike.coe_injective.eq_iff.mpr H

/-- Like `Finsupp'.single_eq_single_iff`, but with a `HEq` due to dependent types -/
theorem single_eq_single_iff (i j : ι) (xi : β i) (xj : β j) :
    DFinsupp'.single d i xi = DFinsupp'.single d j xj ↔ i = j ∧ HEq xi xj ∨ xi = d i ∧ xj = d j := by
  constructor
  · intro h
    by_cases hij : i = j
    · subst hij
      exact Or.inl ⟨rfl, heq_of_eq (DFinsupp'.single_injective h)⟩
    · have h_coe : ⇑(DFinsupp'.single d i xi) = DFinsupp'.single d j xj := congr_arg (⇑) h
      have hci := congr_fun h_coe i
      have hcj := congr_fun h_coe j
      rw [DFinsupp'.single_eq_same] at hci hcj
      rw [DFinsupp'.single_eq_of_ne (Ne.symm hij)] at hci
      rw [DFinsupp'.single_eq_of_ne hij] at hcj
      exact Or.inr ⟨hci, hcj.symm⟩
  · rintro (⟨rfl, hxi⟩ | ⟨hi, hj⟩)
    · rw [eq_of_heq hxi]
    · rw [hi, hj, DFinsupp'.single_eq_self, DFinsupp'.single_eq_self]

/-- `DFinsupp'.single a b` is injective in `a`. For the statement that it is injective in `b`, see
`DFinsupp'.single_injective` -/
theorem single_left_injective {b : ∀ i : ι, β i} (h : ∀ i, b i ≠ d i) :
    Function.Injective (fun i => single d i (b i) : ι → Π₀' i, [β i, d i]) := fun _ _ H =>
  (((single_eq_single_iff _ _ _ _).mp H).resolve_right fun hb => h _ hb.1).left

@[simp]
theorem single_eq_default {i : ι} {xi : β i} : single d i xi = default ↔ xi = d i := by
  rw [← single_eq_self i, single_eq_single_iff]
  simp

theorem filter_single (p : ι → Prop) [DecidablePred p] (i : ι) (x : β i) :
    (single d i x).filter p = if p i then single d i x else default := by
  ext j
  have := apply_ite (fun x : Π₀' i, [β i, d i] => x j) (p i) (single d i x) default
  dsimp at this
  rw [filter_apply, this]
  obtain rfl | hij := Decidable.eq_or_ne i j
  · rfl
  · rw [single_eq_of_ne hij, ite_self, ite_self]

@[simp]
theorem filter_single_pos {p : ι → Prop} [DecidablePred p] (i : ι) (x : β i) (h : p i) :
    (single d i x).filter p = single d i x := by rw [filter_single, if_pos h]

@[simp]
theorem filter_single_neg {p : ι → Prop} [DecidablePred p] (i : ι) (x : β i) (h : ¬p i) :
    (single d i x).filter p = default := by rw [filter_single, if_neg h]

/-- Equality of sigma types is sufficient (but not necessary) to show equality of `DFinsupp'`s. -/
theorem single_eq_of_sigma_eq {i j} {xi : β i} {xj : β j} (h : (⟨i, xi⟩ : Sigma β) = ⟨j, xj⟩) :
    DFinsupp'.single d i xi = DFinsupp'.single d j xj := by
  cases h
  rfl

@[simp]
theorem equivFunOnFintype_single [Fintype ι] (i : ι) (m : β i) :
    (@DFinsupp'.equivFunOnFintype ι β _ _) (DFinsupp'.single d i m) = Function.update d i m := by
  ext x
  dsimp [Pi.single, Function.update]
  simp [DFinsupp'.single_eq_functionUpdate, @eq_comm _ i]

@[simp]
theorem equivFunOnFintype_symm_single [Fintype ι] (i : ι) (m : β i) :
    (@DFinsupp'.equivFunOnFintype ι β _ _).symm (Function.update d i m) = DFinsupp'.single d i m := by
  ext i'
  simp only [← single_eq_functionUpdate, equivFunOnFintype_symm_coe]

section SingleAndZipWith

@[simp]
theorem zipWith_single_single (f : ∀ i, β₁ i → β₂ i → β i) (hf : ∀ i, f i (d₁ i) (d₂ i) = d i)
    {i} (b₁ : β₁ i) (b₂ : β₂ i) :
    zipWith f hf (single d₁ i b₁) (single d₂ i b₂) = single d i (f i b₁ b₂) := by
  ext j
  rw [zipWith_apply]
  obtain rfl | hij := Decidable.eq_or_ne i j
  · rw [single_eq_same, single_eq_same, single_eq_same]
  · rw [single_eq_of_ne hij, single_eq_of_ne hij, single_eq_of_ne hij, hf]

end SingleAndZipWith

/-- Redefine `f i` to be `d i`. -/
def erase (i : ι) (x : Π₀' i, [β i, d i]) : Π₀' i, [β i, d i] :=
  ⟨fun j ↦ if j = i then d j else x.1 j,
    x.support'.map fun xs ↦ ⟨xs.1, fun j ↦ (xs.prop j).imp_right (by simp only [·, ite_self])⟩⟩

@[simp]
theorem erase_apply {i j : ι} {f : Π₀' i, [β i, d i]} :
    (f.erase i) j = if j = i then d j else f j :=
  rfl

-- @[simp] -- Porting note (#10618): simp can prove this
theorem erase_same {i : ι} {f : Π₀' i, [β i, d i]} : (f.erase i) i = d i := by simp

theorem erase_ne {i i' : ι} {f : Π₀' i, [β i, d i]} (h : i' ≠ i) : (f.erase i) i' = f i' := by
  simp [h]

theorem piecewise_single_erase (x : Π₀' i, [β i, d i]) (i : ι)
    [∀ i' : ι, Decidable <| (i' ∈ ({i} : Set ι))] : -- Porting note: added Decidable hypothesis
    (single d i (x i)).piecewise (x.erase i) {i} = x := by
  ext j; rw [piecewise_apply]; split_ifs with h
  · rw [(id h : j = i), single_eq_same]
  · exact erase_ne h

@[simp]
theorem erase_default (i : ι) : erase i (default : Π₀' i, [β i, d i]) = default :=
  ext fun _ => ite_self _

@[simp]
theorem filter_ne_eq_erase (f : Π₀' i, [β i, d i]) (i : ι) : f.filter (· ≠ i) = f.erase i := by
  ext1 j
  simp only [DFinsupp'.filter_apply, DFinsupp'.erase_apply, ite_not]

@[simp]
theorem filter_ne_eq_erase' (f : Π₀' i, [β i, d i]) (i : ι) : f.filter (i ≠ ·) = f.erase i := by
  rw [← filter_ne_eq_erase f i]
  congr with j
  exact ne_comm

theorem erase_single (j : ι) (i : ι) (x : β i) :
    (single d i x).erase j = if i = j then default else single d i x := by
  rw [← filter_ne_eq_erase, filter_single, ite_not]

@[simp]
theorem erase_single_same (i : ι) (x : β i) : (single d i x).erase i = default := by
  rw [erase_single, if_pos rfl]

@[simp]
theorem erase_single_ne {i j : ι} (x : β i) (h : i ≠ j) :
    (single d i x).erase j = single d i x := by
  rw [erase_single, if_neg h]

section update

variable (f : Π₀' i, [β i, d i]) (i) (b : β i)

/-- Replace the value of a `Π₀' i, [β i, d i]` at a given point `i : ι` by a given value `b : β i`.
If `b = 0`, this amounts to removing `i` from the support.
Otherwise, `i` is added to it.

This is the (dependent) finitely-supported version of `Function.update`. -/
def update : Π₀' i, [β i, d i] :=
  ⟨Function.update f i b,
    f.support'.map fun s =>
      ⟨i ::ₘ s.1, fun j => by
        rcases eq_or_ne i j with (rfl | hi)
        · simp
        · obtain hj | (hj : f j = d j) := s.prop j
          · exact Or.inl (Multiset.mem_cons_of_mem hj)
          · exact Or.inr ((Function.update_noteq hi.symm b _).trans hj)⟩⟩

variable (j : ι)

@[simp, norm_cast] lemma coe_update : (f.update i b : ∀ i : ι, β i) = Function.update f i b := rfl

@[simp]
theorem update_self : f.update i (f i) = f := by
  ext
  simp

@[simp]
theorem update_eq_erase : f.update i (d i) = f.erase i := by
  ext j
  rcases eq_or_ne i j with (rfl | hi)
  · simp
  · simp [hi.symm]

end update

end Basic

theorem single_zipWith_erase (f : ∀ i, β i → β i → β i)
    (hf₁ : ∀ i x, f i (d i) x = x) (hf₂ : ∀ i x, f i x (d i) = x)
    (i : ι) (x : Π₀' i, [β i, d i]) :
    zipWith f (fun i ↦ hf₁ _ _) (single d i (x i)) (x.erase i) = x :=
  ext fun i' =>
    if h : i = i' then by
      subst h; simp only [zipWith_apply, single_apply, erase_apply, hf₂, dite_eq_ite, if_true]
    else by
      simp only [zipWith_apply, single_apply, erase_apply, dif_neg h, if_neg (Ne.symm h), hf₁]

protected theorem induction_on {p : (Π₀' i, [β i, d i]) → Prop} (x : Π₀' i, [β i, d i])
    (f : ∀ i, β i → β i → β i) (hf₁ : ∀ i x, f i (d i) x = x) (hf₂ : ∀ i x, f i x (d i) = x)
    (h0 : p default)
    (ha : ∀ (i b) (x : Π₀' i, [β i, d i]), x i = d i → b ≠ d i → p x →
      p (zipWith f (fun i ↦ hf₁ _ _) (single d i b) x)) :
    p x := by
  cases' x with x s
  induction' s using Trunc.induction_on with s
  cases' s with s H
  induction' s using Multiset.induction_on with i s ih generalizing x
  · have : x = d := funext fun i => (H i).resolve_left (Multiset.not_mem_zero _)
    subst this
    exact h0
  have H2 : p (erase i ⟨x, Trunc.mk ⟨i ::ₘ s, H⟩⟩) := by
    dsimp only [erase, Trunc.map, Trunc.bind, Trunc.liftOn, Trunc.lift_mk,
      Function.comp, Subtype.coe_mk]
    have H2 : ∀ j, j ∈ s ∨ ite (j = i) (d j) (x j) = d j := by
      intro j
      cases' H j with H2 H2
      · cases' Multiset.mem_cons.1 H2 with H3 H3
        · right; exact if_pos H3
        · left; exact H3
      right
      split_ifs <;> [rfl; exact H2]
    have H3 : ∀ aux, (⟨fun j : ι => ite (j = i) (d j) (x j), Trunc.mk ⟨i ::ₘ s, aux⟩⟩ :
          Π₀' i, [β i, d i]) =
        ⟨fun j : ι => ite (j = i) (d j) (x j), Trunc.mk ⟨s, H2⟩⟩ :=
      fun _ ↦ ext fun _ => rfl
    rw [H3]
    apply ih
  have H3 : zipWith f (fun i ↦ hf₁ _ _) (single d i _) _ =
      (⟨x, Trunc.mk ⟨i ::ₘ s, H⟩⟩ : Π₀' i, [β i, d i]) :=
    single_zipWith_erase f hf₁ hf₂ _ _
  rw [← H3]
  change p (zipWith _ _ (single d i (x i)) _)
  cases' Classical.em (x i = d i) with h h
  · rw [h, single_eq_self, zipWith_default_left]
    exact H2
  refine' ha _ _ _ _ h H2
  rw [erase_same]

theorem induction_on' {p : (Π₀' i, [β i, d i]) → Prop} (x : Π₀' i, [β i, d i])
    (f : ∀ i, β i → β i → β i) (hf₁ : ∀ i x, f i (d i) x = x) (hf₂ : ∀ i x, f i x (d i) = x)
    (h0 : p default)
    (ha : ∀ (i b) (x : Π₀' i, [β i, d i]), x i = d i → b ≠ d i → p x →
      p (zipWith f (fun i ↦ hf₁ _ _) x (single d i b))) : p x :=
  DFinsupp'.induction_on x (fun i x y ↦ f i y x) hf₂ hf₁ h0 <| by simpa only [zipWith_swap] using ha

section SupportBasic

variable [∀ (i) (x : β i), Decidable (x ≠ d i)]

/-- Set `{i | f x ≠ d i}` as a `Finset`. -/
def support (f : Π₀' i, [β i, d i]) : Finset ι :=
  (f.support'.lift fun xs => (Multiset.toFinset xs.1).filter fun i => f i ≠ d i) <| by
    rintro ⟨sx, hx⟩ ⟨sy, hy⟩
    dsimp only [Subtype.coe_mk, toFun_eq_coe] at *
    ext i; constructor
    · intro H
      rcases Finset.mem_filter.1 H with ⟨_, h⟩
      exact Finset.mem_filter.2 ⟨Multiset.mem_toFinset.2 <| (hy i).resolve_right h, h⟩
    · intro H
      rcases Finset.mem_filter.1 H with ⟨_, h⟩
      exact Finset.mem_filter.2 ⟨Multiset.mem_toFinset.2 <| (hx i).resolve_right h, h⟩

@[simp]
theorem support_mk_subset {s : Finset ι} {x : ∀ i : (↑s : Set ι), β i.1} : (mk d s x).support ⊆ s :=
  fun _ H => Multiset.mem_toFinset.1 (Finset.mem_filter.1 H).1

@[simp]
theorem support_mk'_subset {f : ∀ i, β i} {s : Multiset ι} {h} :
    (mk' f <| Trunc.mk ⟨s, h⟩ : Π₀' i, [β i, d i]).support ⊆ s.toFinset := fun i H =>
  Multiset.mem_toFinset.1 <| by simpa using (Finset.mem_filter.1 H).1

@[simp]
theorem mem_support_toFun (f : Π₀' i, [β i, d i]) (i) : i ∈ f.support ↔ f i ≠ d i := by
  cases' f with f s
  induction' s using Trunc.induction_on with s
  dsimp only [support, Trunc.lift_mk]
  rw [Finset.mem_filter, Multiset.mem_toFinset, coe_mk']
  exact and_iff_right_of_imp (s.prop i).resolve_right

theorem eq_mk_support (f : Π₀' i, [β i, d i]) : f = mk d f.support fun i => f i := by aesop

/-- Equivalence between dependent functions with finite support `s : Finset ι` and functions
`∀ i, {x : β i // x ≠ d i}`. -/
@[simps]
def subtypeSupportEqEquiv (s : Finset ι) :
    {f : Π₀' i, [β i, d i] // f.support = s} ≃ ∀ i : s, {x : β i // x ≠ d i} where
  toFun | ⟨f, hf⟩ => fun ⟨i, hi⟩ ↦ ⟨f i, (f.mem_support_toFun i).1 <| hf.symm ▸ hi⟩
  invFun f := ⟨mk d s fun i ↦ (f i).1, Finset.ext fun i ↦ by
    -- TODO: `simp` fails to use `(f _).2` inside `∃ _, _`
    calc
      i ∈ support (mk d s fun i ↦ (f i).1) ↔ ∃ h : i ∈ s, (f ⟨i, h⟩).1 ≠ d i := by simp
      _ ↔ ∃ _ : i ∈ s, True := exists_congr fun h ↦ (iff_true _).mpr (f _).2
      _ ↔ i ∈ s := by simp⟩
  left_inv := by
    rintro ⟨f, rfl⟩
    ext i
    simpa using Eq.symm
  right_inv f := by
    ext1
    simp [Subtype.eta]; rfl

/-- Equivalence between all dependent finitely supported functions `f : Π₀' i, [β i, d i]` and type
of pairs `⟨s : Finset ι, f : ∀ i : s, {x : β i // x ≠ d i}⟩`. -/
@[simps! apply_fst apply_snd_coe]
def sigmaFinsetFunEquiv : (Π₀' i, [β i, d i]) ≃ Σ s : Finset ι, ∀ i : s, {x : β i // x ≠ d i} :=
  (Equiv.sigmaFiberEquiv DFinsupp'.support).symm.trans (.sigmaCongrRight subtypeSupportEqEquiv)

@[simp]
theorem support_default : (default : Π₀' i, [β i, d i]).support = ∅ :=
  rfl

theorem mem_support_iff {f : Π₀' i, [β i, d i]} {i : ι} : i ∈ f.support ↔ f i ≠ d i :=
  f.mem_support_toFun _

theorem not_mem_support_iff {f : Π₀' i, [β i, d i]} {i : ι} : i ∉ f.support ↔ f i = d i :=
  not_iff_comm.1 mem_support_iff.symm

@[simp]
theorem support_eq_empty {f : Π₀' i, [β i, d i]} : f.support = ∅ ↔ f = default :=
  ⟨fun H => ext <| by simpa [Finset.ext_iff] using H, by simp (config := { contextual := true })⟩

instance decidableDefault : DecidablePred (Eq (default : Π₀' i, [β i, d i])) := fun _ =>
  decidable_of_iff _ <| support_eq_empty.trans eq_comm

theorem support_subset_iff {s : Set ι} {f : Π₀' i, [β i, d i]} :
    ↑f.support ⊆ s ↔ ∀ i ∉ s, f i = d i := by
  simp [Set.subset_def]; exact forall_congr' fun i => not_imp_comm

theorem support_single_ne {i : ι} {b : β i} (hb : b ≠ d i) :
    (single d i b).support = {i} := by
  ext j; by_cases h : i = j
  · subst h
    simp [hb]
  simp [Ne.symm h, h]

theorem support_single_subset {i : ι} {b : β i} : (single d i b).support ⊆ {i} :=
  support_mk'_subset

section MapRangeAndZipWith

theorem mapRange_def [∀ (i) (x : β₁ i), Decidable (x ≠ d₁ i)] {f : ∀ i, β₁ i → β₂ i}
    {hf : ∀ i, f i (d₁ i) = d₂ i} {g : Π₀' i, [β₁ i, d₁ i]} :
    mapRange f hf g = mk d₂ g.support fun i => f i.1 (g i.1) := by
  ext i
  by_cases h : g i ≠ d₁ i <;> simp at h <;> simp [h, hf]

@[simp]
theorem mapRange_single {f : ∀ i, β₁ i → β₂ i} {hf : ∀ i, f i (d₁ i) = d₂ i} {i : ι} {b : β₁ i} :
    mapRange f hf (single d₁ i b) = single d₂ i (f i b) :=
  DFinsupp'.ext fun i' => by
    by_cases h : i = i'
    · subst i'
      simp
    · simp [h, hf]

variable [∀ (i) (x : β₁ i), Decidable (x ≠ d₁ i)] [∀ (i) (x : β₂ i), Decidable (x ≠ d₂ i)]

theorem support_mapRange {f : ∀ i, β₁ i → β₂ i} {hf : ∀ i, f i (d₁ i) = d₂ i}
    {g : Π₀' i, [β₁ i, d₁ i]} : (mapRange f hf g).support ⊆ g.support := by simp [mapRange_def]

theorem zipWith_def {ι : Type u} {β : ι → Type v} {β₁ : ι → Type v₁} {β₂ : ι → Type v₂}
    [dec : DecidableEq ι] {d : ∀ i : ι, β i} {d₁ : ∀ i : ι, β₁ i} {d₂ : ∀ i : ι, β₂ i}
    [∀ (i : ι) (x : β₁ i), Decidable (x ≠ d₁ i)] [∀ (i : ι) (x : β₂ i), Decidable (x ≠ d₂ i)]
    {f : ∀ i, β₁ i → β₂ i → β i} {hf : ∀ i, f i (d₁ i) (d₂ i) = d i}
    {g₁ : Π₀' i, [β₁ i, d₁ i]} {g₂ : Π₀' i, [β₂ i, d₂ i]} :
    zipWith f hf g₁ g₂ = mk d (g₁.support ∪ g₂.support) fun i => f i.1 (g₁ i.1) (g₂ i.1) := by
  ext i
  by_cases h1 : g₁ i ≠ d₁ i <;> by_cases h2 : g₂ i ≠ d₂ i <;> simp only [not_not, Ne] at h1 h2 <;>
    simp [h1, h2, hf]

theorem support_zipWith {f : ∀ i, β₁ i → β₂ i → β i} {hf : ∀ i, f i (d₁ i) (d₂ i) = d i}
    {g₁ : Π₀' i, [β₁ i, d₁ i]} {g₂ : Π₀' i, [β₂ i, d₂ i]} :
    (zipWith f hf g₁ g₂).support ⊆ g₁.support ∪ g₂.support := by
  simp [zipWith_def]

end MapRangeAndZipWith

theorem erase_def (i : ι) (f : Π₀' i, [β i, d i]) :
    f.erase i = mk d (f.support.erase i) fun j => f j.1 := by
  ext j
  by_cases h1 : j = i <;> by_cases h2 : f j ≠ d j <;> simp at h2 <;> simp [h1, h2]

@[simp]
theorem support_erase (i : ι) (f : Π₀' i, [β i, d i]) :
    (f.erase i).support = f.support.erase i := by
  ext j
  by_cases h1 : j = i
  simp only [h1, mem_support_toFun, erase_apply, ite_true, ne_eq, not_true, not_not,
    Finset.mem_erase, false_and]
  by_cases h2 : f j ≠ d j <;> simp at h2 <;> simp [h1, h2]

theorem support_update_ne (f : Π₀' i, [β i, d i]) (i : ι) {b : β i} (h : b ≠ d i) :
    support (f.update i b) = insert i f.support := by
  ext j
  rcases eq_or_ne i j with (rfl | hi)
  · simp [h]
  · simp [hi.symm]

theorem support_update (f : Π₀' i, [β i, d i]) (i : ι) (b : β i) [Decidable (b = d i)] :
    support (f.update i b) = if b = d i then support (f.erase i) else insert i f.support := by
  ext j
  split_ifs with hb
  · subst hb
    simp [update_eq_erase, support_erase]
  · rw [support_update_ne f _ hb]

section FilterAndSubtypeDomain

variable {p : ι → Prop} [DecidablePred p]

theorem filter_def (f : Π₀' i, [β i, d i]) :
    f.filter p = mk d (f.support.filter p) fun i => f i.1 := by
  ext i; by_cases h1 : p i <;> by_cases h2 : f i ≠ d i <;> simp at h2 <;> simp [h1, h2]

@[simp]
theorem support_filter (f : Π₀' i, [β i, d i]) : (f.filter p).support = f.support.filter p := by
  ext i; by_cases h : p i <;> simp [h]

theorem subtypeDomain_def (f : Π₀' i, [β i, d i]) :
    f.subtypeDomain p = mk _ (f.support.subtype p) fun i => f i := by
  ext i; by_cases h2 : f i ≠ d i <;> try simp at h2; dsimp; simp [h2]

@[simp, nolint simpNF] -- Porting note: simpNF claims that LHS does not simplify, but it does
theorem support_subtypeDomain {f : Π₀' i, [β i, d i]} :
    (subtypeDomain p f).support = f.support.subtype p := by
  ext i
  simp

end FilterAndSubtypeDomain

end SupportBasic

instance [∀ i, DecidableEq (β i)] : DecidableEq (Π₀' i, [β i, d i]) := fun f g =>
  decidable_of_iff (f.support = g.support ∧ ∀ i ∈ f.support, f i = g i)
    ⟨fun ⟨h₁, h₂⟩ => ext fun i => if h : i ∈ f.support then h₂ i h else by
      have hf : f i = d i := by rwa [mem_support_iff, not_not] at h
      have hg : g i = d i := by rwa [h₁, mem_support_iff, not_not] at h
      rw [hf, hg],
     by rintro rfl; simp⟩

section Equiv

open Finset

variable {κ : Type*}

/-- Reindexing (and possibly removing) terms of a `DFinsupp'`. -/
noncomputable def comapDomain (h : κ → ι) (hh : Function.Injective h)
    (f : Π₀' i, [β i, d i]) : Π₀' k, [β (h k), d (h k)] where
  toFun x := f (h x)
  support' :=
    f.support'.map fun s =>
      ⟨((Multiset.toFinset s.1).preimage h (hh.injOn _)).val, fun x =>
        (s.prop (h x)).imp_left fun hx => mem_preimage.mpr <| Multiset.mem_toFinset.mpr hx⟩

@[simp]
theorem comapDomain_apply (h : κ → ι) (hh : Function.Injective h) (f : Π₀' i, [β i, d i])
    (k : κ) : comapDomain h hh f k = f (h k) :=
  rfl

@[simp]
theorem comapDomain_default (h : κ → ι) (hh : Function.Injective h) :
    comapDomain h hh (default : Π₀' i, [β i, d i]) = default := by
  ext
  rw [default_apply, comapDomain_apply, default_apply]

@[simp]
theorem comapDomain_single [DecidableEq κ] (h : κ → ι) (hh : Function.Injective h)
    (k : κ) (x : β (h k)) : comapDomain h hh (single d (h k) x) = single _ k x := by
  ext i
  rw [comapDomain_apply]
  obtain rfl | hik := Decidable.eq_or_ne i k
  · rw [single_eq_same, single_eq_same]
  · rw [single_eq_of_ne hik.symm, single_eq_of_ne (hh.ne hik.symm)]

/-- A computable version of comapDomain when an explicit left inverse is provided. -/
def comapDomain' (h : κ → ι) {h' : ι → κ} (hh' : Function.LeftInverse h' h)
    (f : Π₀' i, [β i, d i]) : Π₀' k, [β (h k), d (h k)] where
  toFun x := f (h x)
  support' :=
    f.support'.map fun s =>
      ⟨Multiset.map h' s.1, fun x =>
        (s.prop (h x)).imp_left fun hx => Multiset.mem_map.mpr ⟨_, hx, hh' _⟩⟩

@[simp]
theorem comapDomain'_apply (h : κ → ι) {h' : ι → κ}
    (hh' : Function.LeftInverse h' h) (f : Π₀' i, [β i, d i]) (k : κ) : comapDomain' h hh' f k = f (h k) :=
  rfl

@[simp]
theorem comapDomain'_default (h : κ → ι) {h' : ι → κ}
    (hh' : Function.LeftInverse h' h) : comapDomain' h hh' (default : Π₀' i, [β i, d i]) = default := by
  ext
  rw [default_apply, comapDomain'_apply, default_apply]

/-- Reindexing terms of a `DFinsupp'`.

This is the `DFinsupp'` version of `Equiv.piCongrLeft'`. -/
@[simps apply]
def equivCongrLeft (h : ι ≃ κ) : (Π₀' i, [β i, d i]) ≃ Π₀' k, [β (h.symm k), d (h.symm k)]
    where
  toFun := comapDomain' h.symm h.right_inv
  invFun f :=
    mapRange (fun i => Equiv.cast <| congr_arg β <| h.symm_apply_apply i)
      (fun i => (Equiv.cast_eq_iff_heq _).mpr <| by rw [Equiv.symm_apply_apply])
      (@comapDomain' _ _ _ _ h _ h.left_inv f)
  left_inv f := by
    ext i
    rw [mapRange_apply, comapDomain'_apply, comapDomain'_apply, Equiv.cast_eq_iff_heq,
      h.symm_apply_apply]
  right_inv f := by
    ext k
    rw [comapDomain'_apply, mapRange_apply, comapDomain'_apply, Equiv.cast_eq_iff_heq,
      h.apply_symm_apply]

variable {α : Option ι → Type v} {dα : ∀ i, α i}

/-- Adds a term to a `DFinsupp'`, making a `DFinsupp'` indexed by an `Option`.

This is the `DFinsupp'` version of `Option.rec`. -/
def extendWith (a : α none) (f : Π₀' i, [α (some i), dα (some i)]) : Π₀' i, [α i, dα i] where
  toFun := fun i ↦ match i with | none => a | some _ => f _
  support' :=
    f.support'.map fun s =>
      ⟨none ::ₘ Multiset.map some s.1, fun i =>
        Option.rec (Or.inl <| Multiset.mem_cons_self _ _)
          (fun i =>
            (s.prop i).imp_left fun h => Multiset.mem_cons_of_mem <| Multiset.mem_map_of_mem _ h)
          i⟩

@[simp]
theorem extendWith_none (f : Π₀' i, [α (some i), dα (some i)]) (a : α none) :
    f.extendWith a none = a :=
  rfl

@[simp]
theorem extendWith_some (f : Π₀' i, [α (some i), dα (some i)]) (a : α none) (i : ι) :
    f.extendWith a (some i) = f i :=
  rfl

@[simp]
theorem extendWith_single [DecidableEq ι] (i : ι) (x : α (some i)) :
    (single _ i x).extendWith (dα none) = single dα (some i) x := by
  ext (_ | j)
  · rw [extendWith_none, single_eq_of_ne (Option.some_ne_none _)]
  · rw [extendWith_some]
    obtain rfl | hij := Decidable.eq_or_ne i j
    · rw [single_eq_same, single_eq_same]
    · rw [single_eq_of_ne hij, single_eq_of_ne ((Option.some_injective _).ne hij)]

@[simp]
theorem extendWith_default [DecidableEq ι] (x : α none) :
    (default : Π₀' i, [α (some i), dα (some i)]).extendWith x = single dα none x := by
  ext (_ | j)
  · rw [extendWith_none, single_eq_same]
  · rw [extendWith_some, single_eq_of_ne (Option.some_ne_none _).symm, default_apply]

/-- Bijection obtained by separating the term of index `none` of a `DFinsupp'` over `Option ι`.

This is the `DFinsupp'` version of `Equiv.piOptionEquivProd`. -/
@[simps]
noncomputable def equivProdDFinsupp' :
    (Π₀' i, [α i, dα i]) ≃ α none × Π₀' i, [α (some i), dα (some i)] where
  toFun f := (f none, comapDomain some (Option.some_injective _) f)
  invFun f := f.2.extendWith f.1
  left_inv f := by
    ext i; cases' i with i
    · rw [extendWith_none]
    · rw [extendWith_some, comapDomain_apply]
  right_inv x := by
    dsimp only
    ext
    · exact extendWith_none x.snd _
    · rw [comapDomain_apply, extendWith_some]

end Equiv

section ProdAndSum

/-- `DFinsupp'.prod f g` is the product of `g i (f i)` over the support of `f`. -/
@[to_additive "`DFinsupp'.sum f g` is the sum of `g i (f i)` over the support of `f`."]
def prod [∀ (i) (x : β i), Decidable (x ≠ d i)] [CommMonoid γ] (f : Π₀' i, [β i, d i])
    (g : ∀ i, β i → γ) : γ :=
  ∏ i in f.support, g i (f i)

@[to_additive (attr := simp)]
theorem _root_.map_dfinsupp'_prod
    {R S H : Type*} [∀ (i) (x : β i), Decidable (x ≠ d i)] [CommMonoid R] [CommMonoid S]
    [FunLike H R S] [MonoidHomClass H R S] (h : H) (f : Π₀' i, [β i, d i])
    (g : ∀ i, β i → R) : h (f.prod g) = f.prod fun a b => h (g a b) :=
  map_prod _ _ _

@[to_additive]
theorem prod_mapRange_index
    [∀ (i) (x : β₁ i), Decidable (x ≠ d₁ i)] [∀ (i) (x : β₂ i), Decidable (x ≠ d₂ i)]
    [CommMonoid γ] {f : ∀ i, β₁ i → β₂ i} {hf : ∀ i, f i (d₁ i) = d₂ i}
    {g : Π₀' i, [β₁ i, d₁ i]} {h : ∀ i, β₂ i → γ}
    (h0 : ∀ i, h i (d₂ i) = 1) : (mapRange f hf g).prod h = g.prod fun i b => h i (f i b) := by
  rw [mapRange_def]
  refine' (Finset.prod_subset support_mk_subset _).trans _
  · intro i h1 h2
    simp only [mem_support_toFun, ne_eq] at h1
    simp only [Finset.coe_sort_coe, mem_support_toFun, mk_apply, ne_eq, h1, not_false_iff,
      dite_eq_ite, ite_true, not_not] at h2
    simp [h2, h0]
  · refine' Finset.prod_congr rfl _
    intro i h1
    simp only [mem_support_toFun, ne_eq] at h1
    simp [h1]

@[to_additive]
theorem prod_default_index [∀ i, AddCommMonoid (β i)] [∀ (i) (x : β i), Decidable (x ≠ d i)]
    [CommMonoid γ] {h : ∀ i, β i → γ} : (default : Π₀' i, [β i, d i]).prod h = 1 :=
  rfl

@[to_additive]
theorem prod_single_index [∀ (i) (x : β i), Decidable (x ≠ d i)] [CommMonoid γ]
    {i : ι} {b : β i} {h : ∀ i, β i → γ} (hd : h i (d i) = 1) :
    (single d i b).prod h = h i b := by
  by_cases h : b ≠ d i
  · simp [DFinsupp'.prod, support_single_ne h]
  · rw [not_not] at h
    simp [h, prod_default_index, hd]

@[to_additive]
theorem prod_comm {ι₁ ι₂ : Sort _} {β₁ : ι₁ → Type*} {β₂ : ι₂ → Type*} [DecidableEq ι₁]
    [DecidableEq ι₂] {d₁ : ∀ i, β₁ i} {d₂ : ∀ i, β₂ i} [∀ (i) (x : β₁ i), Decidable (x ≠ d₁ i)]
    [∀ (i) (x : β₂ i), Decidable (x ≠ d₂ i)] [CommMonoid γ] (f₁ : Π₀' i, [β₁ i, d₁ i])
    (f₂ : Π₀' i, [β₂ i, d₂ i]) (h : ∀ i, β₁ i → ∀ i, β₂ i → γ) :
    (f₁.prod fun i₁ x₁ => f₂.prod fun i₂ x₂ => h i₁ x₁ i₂ x₂) =
      f₂.prod fun i₂ x₂ => f₁.prod fun i₁ x₁ => h i₁ x₁ i₂ x₂ :=
  Finset.prod_comm

@[to_additive (attr := simp)]
theorem prod_one [∀ i, AddCommMonoid (β i)] [∀ (i) (x : β i), Decidable (x ≠ d i)] [CommMonoid γ]
    {f : Π₀' i, [β i, d i]} : (f.prod fun _ _ => (1 : γ)) = 1 :=
  Finset.prod_const_one

@[to_additive (attr := simp)]
theorem prod_mul [∀ i, AddCommMonoid (β i)] [∀ (i) (x : β i), Decidable (x ≠ d i)] [CommMonoid γ]
    {f : Π₀' i, [β i, d i]} {h₁ h₂ : ∀ i, β i → γ} :
    (f.prod fun i b => h₁ i b * h₂ i b) = f.prod h₁ * f.prod h₂ :=
  Finset.prod_mul_distrib

@[to_additive (attr := simp)]
theorem prod_inv [∀ i, AddCommMonoid (β i)] [∀ (i) (x : β i), Decidable (x ≠ d i)] [CommGroup γ]
    {f : Π₀' i, [β i, d i]} {h : ∀ i, β i → γ} : (f.prod fun i b => (h i b)⁻¹) = (f.prod h)⁻¹ :=
  (map_prod (invMonoidHom : γ →* γ) _ f.support).symm

@[to_additive]
theorem prod_eq_one [∀ (i) (x : β i), Decidable (x ≠ d i)] [CommMonoid γ]
    {f : Π₀' i, [β i, d i]} {h : ∀ i, β i → γ} (hyp : ∀ i, h i (f i) = 1) : f.prod h = 1 :=
  Finset.prod_eq_one fun i _ => hyp i

theorem smul_sum {α : Type*} [Monoid α] [∀ (i) (x : β i), Decidable (x ≠ d i)]
    [AddCommMonoid γ] [DistribMulAction α γ] {f : Π₀' i, [β i, d i]} {h : ∀ i, β i → γ} {c : α} :
    c • f.sum h = f.sum fun a b => c • h a b :=
  Finset.smul_sum

@[to_additive]
theorem _root_.dfinsupp_prod_mem [∀ (i) (x : β i), Decidable (x ≠ d i)]
    [CommMonoid γ] {S : Type*} [SetLike S γ] [SubmonoidClass S γ]
    (s : S) (f : Π₀' i, [β i, d i]) (g : ∀ i, β i → γ)
    (h : ∀ c, f c ≠ d c → g c (f c) ∈ s) : f.prod g ∈ s :=
  prod_mem fun _ hi => h _ <| mem_support_iff.1 hi

@[to_additive (attr := simp)]
theorem prod_eq_prod_fintype [Fintype ι] [∀ (i : ι) (x : β i), Decidable (x ≠ d i)]
    -- Porting note: `f` was a typeclass argument
    [CommMonoid γ] (v : Π₀' i, [β i, d i]) {f : ∀ i, β i → γ} (hf : ∀ i, f i (d i) = 1) :
    v.prod f = ∏ i, f i (DFinsupp'.equivFunOnFintype v i) := by
  suffices (∏ i in v.support, f i (v i)) = ∏ i, f i (v i) by simp [DFinsupp'.prod, this]
  apply Finset.prod_subset v.support.subset_univ
  intro i _ hi
  rw [mem_support_iff, not_not] at hi
  rw [hi, hf]

section CommMonoidWithZero
variable [CommMonoidWithZero γ] [Nontrivial γ] [NoZeroDivisors γ]
  [Π i, DecidableEq (β i)] {f : Π₀' i, [β i, d i]} {g : Π i, β i → γ}

@[simp]
lemma prod_eq_zero_iff : f.prod g = 0 ↔ ∃ i ∈ f.support, g i (f i) = 0 := Finset.prod_eq_zero_iff
lemma prod_ne_zero_iff : f.prod g ≠ 0 ↔ ∀ i ∈ f.support, g i (f i) ≠ 0 := Finset.prod_ne_zero_iff

end CommMonoidWithZero

@[to_additive]
theorem prod_subtypeDomain_index [∀ (i) (x : β i), Decidable (x ≠ d i)]
    [CommMonoid γ] {v : Π₀' i, [β i, d i]} {p : ι → Prop} [DecidablePred p] {h : ∀ i, β i → γ}
    (hp : ∀ x ∈ v.support, p x) : (v.subtypeDomain p).prod (fun i b => h i b) = v.prod h := by
  refine Finset.prod_bij (fun p _ ↦ p) ?_ ?_ ?_ ?_ <;> aesop

end ProdAndSum

end DFinsupp'

section

variable [DecidableEq ι]

namespace MonoidHom

variable {R S : Type*}
variable [∀ (i) (x : β i), Decidable (x ≠ d i)]

@[to_additive (attr := simp, norm_cast)]
theorem coe_dfinsupp'_prod [Monoid R] [CommMonoid S] (f : Π₀' i, [β i, d i]) (g : ∀ i, β i → R →* S) :
    ⇑(f.prod g) = f.prod fun a b => ⇑(g a b) :=
  coe_finset_prod _ _

@[to_additive]
theorem dfinsupp'_prod_apply [Monoid R] [CommMonoid S] (f : Π₀' i, [β i, d i]) (g : ∀ i, β i → R →* S)
    (r : R) : (f.prod g) r = f.prod fun a b => (g a b) r :=
  finset_prod_apply _ _ _

end MonoidHom

end

section FiniteInfinite

instance DFinsupp'.fintype {ι : Type*} {π : ι → Type*} [DecidableEq ι] {dπ : ∀ i, π i}
    [Fintype ι] [∀ i, Fintype (π i)] : Fintype (Π₀' i, [π i, dπ i]) :=
  Fintype.ofEquiv (∀ i, π i) DFinsupp'.equivFunOnFintype.symm

instance DFinsupp'.infinite_of_left {ι : Type*} {π : ι → Type*} [∀ i, Nontrivial (π i)]
    {dπ : ∀ i, π i} [Infinite ι] : Infinite (Π₀' i, [π i, dπ i]) := by
  letI := Classical.decEq ι; choose m hm using fun i => exists_ne (dπ i : π i);
    exact Infinite.of_injective _ (DFinsupp'.single_left_injective hm)

/-- See `DFinsupp'.infinite_of_right` for this in instance form, with the drawback that
it needs all `π i` to be infinite. -/
theorem DFinsupp'.infinite_of_exists_right {ι : Type*} {π : ι → Type*} (i : ι) [Infinite (π i)]
    {dπ : ∀ i, π i} : Infinite (Π₀' i, [π i, dπ i]) :=
  letI := Classical.decEq ι
  Infinite.of_injective (fun j => DFinsupp'.single dπ i j) DFinsupp'.single_injective

/-- See `DFinsupp'.infinite_of_exists_right` for the case that only one `π ι` is infinite. -/
instance DFinsupp'.infinite_of_right {ι : Type*} {π : ι → Type*} [∀ i, Infinite (π i)]
    {dπ : ∀ i, π i} [Nonempty ι] : Infinite (Π₀' i, [π i, dπ i]) :=
  DFinsupp'.infinite_of_exists_right (Classical.arbitrary ι)

end FiniteInfinite
