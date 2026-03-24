import Lake
open Lake DSL

package «analysis-tao-chapters» where
  version := v!"0.1.0"
  keywords := #["math", "analysis", "tao"]
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

-- Require mathlib (same version as the analysis repo for compatibility)
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.23.0-rc2"
