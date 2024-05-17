import Lake
open Lake DSL

package algorithm where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`pp.proofs.withType, false⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "master"
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4.git" @ "main"

@[default_target]
lean_lib Algorithm {
  roots := #[`Algorithm]
}
