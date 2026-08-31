import Lake

open Lake DSL

package "berry-esseen" where
  version := v!"0.1.0"
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`relaxedAutoImplicit, false⟩,
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.29.1"

require «StatLean» from git
  "https://github.com/StatLean/Stat-Lean.git" @
    "e1ef06bf52d2a8896439c5b59d982d9aad28a254"

@[default_target]
lean_lib BerryEsseen where
  roots := #[`BerryEsseen]
