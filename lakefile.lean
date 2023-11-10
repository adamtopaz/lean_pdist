import Lake
open Lake DSL

package «lean_pdist» {
  -- add package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

@[default_target]
lean_lib «PDist» {
  -- add library configuration options here
}
