import Lake
open Lake DSL

package «lean-proofs-1» where
  name := "lean-proofs-1"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "master"

lean_lib «LeanProofs1» where
