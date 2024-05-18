import Algorithm.Data.Mutable

universe u

def Thunk' (α : Type u) : Type u := Mutable (Unit → α)

variable {α : Type u}

def Thunk'.mk (fn : Unit → α) : Thunk' α := Mutable.mk fn

protected def Thunk'.pure (a : α) : Thunk' α :=
  .mk fun _ ↦ a

protected def Thunk'.get (x : Thunk' α) : α :=
  Mutable.getWith₂ x (fun f ↦ f ()) (fun a _ ↦ a) (fun _ ↦ rfl)

/-! lean4/tests/compiler/thunk.lean -/

def compute (v : Nat) : Thunk' Nat :=
  .mk (fun _ => let xs := List.replicate 100000 v; xs.foldl Nat.add 0)

@[noinline]
def test (t : Thunk' Nat) (n : Nat) : Nat :=
  n.repeat (fun r => t.get + r) 0

def main : IO UInt32 :=
  IO.println (toString (test (compute 1) 100000)) *>
  pure 0

#eval main
