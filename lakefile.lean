import Lake
open Lake DSL

package «KissingNumber» where
  -- add package configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

@[default_target]
lean_lib «KissingNumber» where
  -- add library configuration options here
