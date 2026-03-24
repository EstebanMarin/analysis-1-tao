import Lake
open Lake DSL

package «natural-numbers-game» where
  version := v!"0.1.0"
  keywords := #["math", "game"]
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «NaturalNumbers» where
  globs := #[.andSubmodules `NaturalNumbers]
