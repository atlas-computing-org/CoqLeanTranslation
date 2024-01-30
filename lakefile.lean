import Lake
open Lake DSL

package «coq_lean_translation» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «CoqLeanTranslation» {
  -- add any library configuration options here
}
