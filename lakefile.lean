import Lake
open Lake DSL

package "two-doors-proof" where
  version := v!"0.1.0"
  packagesDir := "../lib/packages"

require mathlib from "../lib/mathlib4"

@[default_target]
lean_lib «TwoDoorsProof» where
