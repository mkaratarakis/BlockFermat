import Lake
open Lake DSL

package «blockchain» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «blockchain» {
  -- add any library configuration options here
}
