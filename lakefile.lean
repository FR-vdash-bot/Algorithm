import Lake
open Lake DSL

package algorithm where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`pp.proofs.withType, false⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]
  moreLinkArgs := #[
    "-L./.lake/build/lib",
    "-lstdc++"
  ]

require "leanprover-community" / "mathlib" @ git "master"
require "leanprover" / "doc-gen4" @ git "main"

lean_lib Mutable where
  roots := #[`Mutable]
  precompileModules := true

@[default_target]
lean_lib Algorithm where
  roots := #[`Algorithm]

target ffi.o pkg : FilePath := do
  let oFile := pkg.buildDir / "cpp" / "ffi.o"
  let srcJob ← inputBinFile <| pkg.dir / "cpp" / "ffi.cpp"
  let weakArgs := #["-I", (← getLeanIncludeDir).toString]
  buildO oFile srcJob weakArgs #["-fPIC"] "clang++" getLeanTrace

extern_lib libleanffi pkg := do
  let name := nameToStaticLib "leanffi"
  let ffiO ← ffi.o.fetch
  buildStaticLib (pkg.nativeLibDir / name) #[ffiO]

-- @[test_driver]
-- lean_exe test where
--   srcDir := "scripts"
