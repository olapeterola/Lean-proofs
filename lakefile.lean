import Lake
open Lake DSL

package «Lean-proofs» where
  name := "Lean-proofs"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "master"

lean_lib «LeanProofs» where
