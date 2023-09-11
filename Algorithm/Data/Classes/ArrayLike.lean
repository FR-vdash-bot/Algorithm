/-
Copyright (c) 2023 Yuyang Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuyang Zhao
-/
import Algorithm.Data.Classes.StackLike

class DynamicArrayLike (A : Type*) (α : outParam Type*) extends StackLike A α where
  get a : Fin (size a) → α
  get_toArray a i : (toArray a).get i = get a (i.cast (size_toArray a))

section
variable {α : Type*}

instance : DynamicArrayLike (Array α) α where
  get := Array.get
  get_toArray _ _ := rfl

end

-- TODO: define `get?` `getD`?