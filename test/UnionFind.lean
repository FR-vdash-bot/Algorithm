import Algorithm.Data.UnionFind

abbrev Vector := Batteries.Vector
abbrev UF := UnionFind (Fin 10) (Vector (Fin 10) 10) (Vector Nat 10)

#eval show IO Unit from do
  let mut uf : UF := default
  IO.println (uf.find 1)
  uf := uf.union 1 2
  uf := uf.union 3 4
  uf := uf.union 2 4
  IO.println ((Quot.unquot (Mutable.get uf)).val.parent[(1 : Fin 10)])

#eval show IO Unit from do
  let mut uf : UF := default
  IO.println (uf.find 1)
  uf := uf.union 1 2
  uf := uf.union 3 4
  uf := uf.union 2 4
  IO.println (uf.find 1)
  IO.println ((Quot.unquot (Mutable.get uf)).val.parent[(1 : Fin 10)])
