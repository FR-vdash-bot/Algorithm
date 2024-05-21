/-
Copyright (c) 2024 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/

/-!
# Mutable

-/

universe u v

-- waiting lean4#2292
/-
structure Mutable (α : Type u) : Type u where
  mk ::
  get : α

attribute [extern "lean_mk_Mutable"] Mutable.mk
attribute [extern "lean_Mutable_get"] Mutable.get

variable {α : Type u}

@[extern "lean_Mutable_get_with"]
protected def Mutable.getWith (x : @& Mutable α) (f : α → α) : α :=
  x.get
-/

structure Mutable (α : Type u) : Type u where
  private __mk__ ::
  private __get__ : α

namespace Mutable
variable {α : Type u} {β : Type v}

@[extern "lean_mk_Mutable"]
def mk (a : α) : Mutable α := __mk__ a

@[extern "lean_Mutable_get"]
def get (a : @& Mutable α) : α := __get__ a

theorem ext {x y : Mutable α} (get : x.get = y.get) : x = y :=
  match x, y, get with | ⟨_⟩, ⟨_⟩, rfl => rfl

theorem ext_iff {x y : Mutable α} : x = y ↔ x.get = y.get :=
  ⟨congrArg get, ext⟩

@[simp]
theorem mk_eq_mk {x y : α} : mk x = mk y ↔ x = y :=
  ext_iff

set_option linter.unusedVariables false in
@[extern "lean_Mutable_modify"]
unsafe def getModifyUnsafe (x : @& Mutable α) (f : α → α) : α :=
  x.get

set_option linter.unusedVariables false in
unsafe abbrev getModifyImpl (x : Mutable α)
    (f : α → α) (hf : ∀ a, f a = a) : α :=
  Mutable.getModifyUnsafe x f

@[implemented_by Mutable.getModifyImpl]
def getModify (x : Mutable α)
    (f : α → α) (hf : ∀ a, f a = a) : α :=
  f x.get

set_option linter.unusedVariables false in
@[extern "lean_Mutable_modify2"]
unsafe def getModify₂Unsafe (x : @& Mutable α) (f : α → β × α) : β :=
  (f x.get).fst

set_option linter.unusedVariables false in
unsafe abbrev getModify₂Impl (x : Mutable α)
    (f : α → β × α) (hgf : ∀ a, (f a).snd = a) : β :=
  Mutable.getModify₂Unsafe x f

@[implemented_by Mutable.getModify₂Impl]
def getModify₂ (x : Mutable α)
    (f : α → β × α) (hgf : ∀ a, (f a).snd = a) : β :=
  (f x.get).fst

end Mutable
