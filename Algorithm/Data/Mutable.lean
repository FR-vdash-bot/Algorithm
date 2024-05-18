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

@[match_pattern, extern "lean_Mutable_get"]
def get (a : @& Mutable α) : α := __get__ a

set_option linter.unusedVariables false in
@[extern "lean_Mutable_modify"]
unsafe def modify (x : @& Mutable α) (f : α → α) : α :=
  x.get

set_option linter.unusedVariables false in
unsafe def getWithImpl (x : Mutable α)
    (f : α → α) (hf : ∀ a, f a = a) : α :=
  Mutable.modify x f

@[implemented_by Mutable.getWithImpl]
def getWith (x : Mutable α)
    (f : α → α) (hf : ∀ a, f a = a) : α :=
  f x.get

set_option linter.unusedVariables false in
@[extern "lean_Mutable_modify2"]
unsafe def modify₂ (x : @& Mutable α) (f : α → β) (g : β → α) : β :=
  f x.get

set_option linter.unusedVariables false in
unsafe def getWith₂Impl (x : Mutable α)
    (f : α → β) (g : β → α) (hgf : ∀ a, g (f a) = a) : β :=
  Mutable.modify₂ x f g

@[implemented_by Mutable.getWith₂Impl]
def getWith₂ (x : Mutable α)
    (f : α → β) (g : β → α) (hgf : ∀ a, g (f a) = a) : β :=
  f x.get

end Mutable
