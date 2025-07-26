import Lake
open Lake DSL

package "LeanTool" where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require Hammer from git "https://github.com/JOSHCLUNE/LeanHammer" @ "main"


require "leanprover-community" / "mathlib" @ git "v4.20.1"


@[default_target]
lean_lib «LeanTool» where
  -- add any library configuration options here
