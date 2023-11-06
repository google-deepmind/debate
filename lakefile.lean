import Lake
open Lake DSL

def moreServerArgs := #[
  "-Dpp.unicode.fun=true", -- pretty-prints `fun a ↦ b`
  "-Dpp.proofs.withType=false",
  "-DautoImplicit=false",
  "-DrelaxedAutoImplicit=false"
]

-- These settings only apply during `lake build`, but not in VSCode editor.
def moreLeanArgs := moreServerArgs

package debate

require mathlib from git "https://github.com/leanprover-community/mathlib4"

@[default_target]
lean_lib Debate where
  moreLeanArgs := moreLeanArgs

lean_lib Prob where
  moreLeanArgs := moreLeanArgs

lean_lib Comp where
  moreLeanArgs := moreLeanArgs

lean_lib Misc where
  moreLeanArgs := moreLeanArgs
