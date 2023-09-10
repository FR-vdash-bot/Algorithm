import Lake
open Lake DSL

package algorithm {
  moreServerArgs := #["-DautoImplicit=false"]
}

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "master"

@[default_target]
lean_lib Algorithm {
  roots := #[`Algorithm]
  moreLeanArgs := #["-DautoImplicit=false"]
}
