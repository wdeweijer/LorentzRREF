import Lake
open Lake DSL

package «lorentzRREF» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «LorentzRREF» {
  -- add any library configuration options here
}
