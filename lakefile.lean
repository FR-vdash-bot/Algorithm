import Lake

open Lake DSL

require "leanprover-community" / "mathlib" @ git "v4.19.0"
require "leanprover" / "doc-gen4" @ git "v4.19.0"

abbrev algorithmOnlyLinters : Array LeanOption := #[
  ⟨`linter.hashCommand, true⟩,
  ⟨`linter.oldObtain, true⟩,
  ⟨`linter.style.cdot, true⟩,
  ⟨`linter.style.dollarSyntax, true⟩,
  ⟨`linter.style.header, true⟩,
  ⟨`linter.style.lambdaSyntax, true⟩,
  ⟨`linter.style.longLine, true⟩,
  ⟨`linter.style.longFile, .ofNat 1500⟩,
  ⟨`linter.style.maxHeartbeats, true⟩,
  -- `latest_import.yml` uses this comment: if you edit it, make sure that the workflow still works
  ⟨`linter.style.missingEnd, true⟩,
  ⟨`linter.style.multiGoal, true⟩,
  ⟨`linter.style.openClassical, true⟩,
  ⟨`linter.style.refine, true⟩,
  ⟨`linter.style.setOption, true⟩
]

abbrev algorithmLeanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`autoImplicit, false⟩
  ] ++ -- options that are used in `lake build`
    algorithmOnlyLinters.map fun s ↦ { s with name := `weak ++ s.name }

package algorithm where

lean_lib Mutable where
  roots := #[`Mutable]
  precompileModules := true

@[default_target]
lean_lib Algorithm where
  leanOptions := algorithmLeanOptions
  moreLinkArgs := #[
    "-L./.lake/build/lib",
    "-lstdc++"
  ]

target ffi.o pkg : System.FilePath := do
  let oFile := pkg.buildDir / "cpp" / "ffi.o"
  let srcJob ← inputBinFile <| pkg.dir / "cpp" / "ffi.cpp"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString]
  buildO oFile srcJob weakArgs #["-fPIC"] "clang++" getLeanTrace

extern_lib libleanffi pkg := do
  let name := nameToStaticLib "leanffi"
  let ffiO ← ffi.o.fetch
  buildStaticLib (pkg.staticLibDir / name) #[ffiO]

-- @[test_driver]
-- lean_exe test where
--   srcDir := "scripts"
